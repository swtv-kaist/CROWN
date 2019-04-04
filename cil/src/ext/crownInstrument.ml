(* Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
 *
 * This file is part of CROWN, which is distributed under the revised
 * BSD license.  A copy of this license can be found in the file LICENSE.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
 * for details.
 *)

open Cil
open Formatcil

let isMainInFile = ref false;;

(*
 * Utilities that should be in the O'Caml standard libraries.
 *)

let isSome o =
  match o with
    | Some _ -> true
    | None   -> false

let rec mapOptional f ls =
  match ls with
    | [] -> []
    | (x::xs) -> (match (f x) with
                    | None -> mapOptional f xs
                    | Some x' -> x' :: mapOptional f xs)

let concatMap f ls =
  let rec doIt res ls =
    match ls with
      | [] -> List.rev res
      | (x::xs) -> doIt (List.rev_append (f x) res) xs
  in
    doIt [] ls

let open_append fname =
  open_out_gen [Open_append; Open_creat; Open_text] 0o700 fname

(*
 * We maintain several bits of state while instrumenting a program:
 *  - the last id assigned to an instrumentation call
 *    (equal to the number of such inserted calls)
 *  - the last id assigned to a statement in the program
 *    (equal to the number of CFG-transformed statements)
 *  - the last id assigned to a function
 *  - the set of all branches seen so far (stored as pairs of branch
 *    id's -- with paired true and false branches stored together),
 *    annotating branches with the funcion they are in
 *  - a per-function control-flow graph (CFG), along with all calls
 *    between functions
 *  - a map from function names to the first statement ID in the function
 *    (to build the complete CFG once all files have been processed)
 *
 * Because the CIL executable will be run once per source file in the
 * instrumented program, we must save/restore this state in files
 * between CIL executions.  (These last two bits of state are
 * write-only -- at the end of each run we just append updates.)
 *)

let idCount = ref 0
let stmtCount = Cfg.start_id
let funCount = ref 0
let branches = ref []
let curBranches = ref []
(* Control-flow graph is stored inside the CIL AST. *)

let getNewId () = ((idCount := !idCount + 1); !idCount)
let addBranchPair bp = (curBranches := bp :: !curBranches)
let addFunction () = (branches := (!funCount, !curBranches) :: !branches;
          curBranches := [];
          funCount := !funCount + 1)

let readCounter fname =
  try
    let f = open_in fname in
      Scanf.fscanf f "%d" (fun x -> x)
  with x -> 0

let writeCounter fname (cnt : int) =
  try
    let f = open_out fname in
      Printf.fprintf f "%d\n" cnt ;
      close_out f
  with x ->
    failwith ("Failed to write counter to: " ^ fname ^ "\n")

let readIdCount () = (idCount := readCounter "idcount")
let readStmtCount () = (stmtCount := readCounter "stmtcount")
let readFunCount () = (funCount := readCounter "funcount")

let writeIdCount () = writeCounter "idcount" !idCount
let writeStmtCount () = writeCounter "stmtcount" !stmtCount
let writeFunCount () = writeCounter "funcount" !funCount

let writeBranches () =
  let writeFunBranches out (fid, bs) =
    if (fid > 0) then
      (let sorted = List.sort compare bs in
         Printf.fprintf out "%d %d\n" fid (List.length bs) ;
         List.iter (fun (s,d) -> Printf.fprintf out "%d %d\n" s d) sorted)
  in
    try
      let f = open_append "branches" in
      let allBranches = (!funCount, !curBranches) :: !branches in
        List.iter (writeFunBranches f) (List.tl (List.rev allBranches));
        close_out f
    with x ->
      prerr_string "Failed to write branches.\n"

(* Visitor which walks the CIL AST, printing the (already computed) CFG. *)
class writeCfgVisitor out firstStmtIdMap =
object (self)
  inherit nopCilVisitor
  val out = out
  val firstStmtIdMap = firstStmtIdMap

  method writeCfgCall f =
    if List.mem_assq f firstStmtIdMap then
      Printf.fprintf out " %d" (List.assq f firstStmtIdMap).sid
    else
      Printf.fprintf out " %s" f.vname

  method writeCfgInst i =
     match i with
         Call(_, Lval(Var f, _), _, _) -> self#writeCfgCall f
       | _ -> ()

  method vstmt(s) =
    Printf.fprintf out "%d" s.sid ;
    List.iter (fun dst -> Printf.fprintf out " %d" dst.sid) s.succs ;
    (match s.skind with
         Instr is -> List.iter self#writeCfgInst is
       | _       -> ()) ;
    output_string out "\n" ;
    DoChildren

end

let writeCfg cilFile firstStmtIdMap =
  try
    let out = open_append "cfg" in
    let wcfgv = new writeCfgVisitor out firstStmtIdMap in
    visitCilFileSameGlobals (wcfgv :> cilVisitor) cilFile ;
    close_out out
  with x ->
    prerr_string "Failed to write CFG.\n"

let buildFirstStmtIdMap cilFile =
  let getFirstFuncStmtId glob =
    match glob with
      | GFun(f, _) -> Some (f.svar, List.hd f.sbody.bstmts)
      | _ -> None
  in
    mapOptional getFirstFuncStmtId cilFile.globals

let writeFirstStmtIdMap firstStmtIdMap =
  let writeEntry out (f,s) =
    (* To help avoid "collisions", skip static functions. *)
    (*if not (f.vstorage = Static) then*)
      Printf.fprintf out "%s %d\n" f.vname s.sid
  in
  try
    let out = open_append "cfg_func_map" in
    List.iter (writeEntry out) firstStmtIdMap ;
    close_out out
  with x ->
    prerr_string "Failed to write (function, first statement ID) map.\n"

let handleCallEdgesAndWriteCfg cilFile =
  let stmtMap = buildFirstStmtIdMap cilFile in
   writeCfg cilFile stmtMap ;
   writeFirstStmtIdMap stmtMap


(* Utilities *)

let noAddr = zero

let shouldSkipFunction f = 
    let skipByAttribute = if (hasAttribute "crown_skip" f.vattr || 
                          hasAttribute "crest_skip" f.vattr || (* for legacy *)
                          hasAttribute "always_inline" f.vattr ||
                          hasAttribute "gnu_inline" f.vattr)
    then true else false in
    let skipRegexp = Str.regexp "^__" in
    let skipByName = Str.string_match skipRegexp f.vname 0 in
    let skipInline = f.vinline in
    (*Printf.printf "Func: %s\n" f.vname;*)
    let attrstr attr = 
      match attr with
      | Attr (astr, _) -> Printf.printf "%s " astr;
    in
    List.iter attrstr f.vattr;
    (*Printf.printf "\n";*)
    if (f.vinline == true) then Printf.printf "inline\n" else Printf.printf "no inline\n";
    (*Printf.printf "%B %B %B\n" skipByAttribute skipByName skipInline;*)
    skipByAttribute || skipByName || skipInline

let isProbeFunction f = 
    let probeRegexp = Str.regexp "^__Crown" in
    Str.string_match probeRegexp f.vname 0

let prependToBlock (is : instr list) (b : block) =
  b.bstmts <- mkStmt (Instr is) :: b.bstmts

(* Should we instrument sub-expressions of a given type? *)
let isSymbolicType ty =
  match (unrollType ty) with
   | TInt _ | TPtr _ | TEnum _ | TFloat _ -> true
   | _ -> false
let isSymbolicFpType ty = 
  match (unrollType ty) with
   | TInt _ | TEnum _ | TFloat _ -> true
   | _ -> false

let isStructureType ty =
  match (unrollType ty) with
    | TComp _ -> true
    | _ -> false

let isSignedType ty =
  match (unrollType ty) with
    | TInt (kind, _) -> isSigned kind
    | _ -> false

(*
 * written by Hyunwoo Kim (17.07.13)
 * Define type for line number and file name.
 *)
let lineType = intType
let fnameType = charPtrType

(* These definitions must match those in "libcrown/crown.h". *)
let idType   = intType
let bidType  = intType
let fidType  = uintType
let valType  = TInt (ILongLong, [])
let valFpType = TFloat (FDouble, [])
let addrType = TInt (IULong, [])
let boolType = TInt (IUChar, [])
let opType   = intType  (* enum *)
let typeType = intType  (* enum *)
let charptrType = TPtr( TInt (IChar, []), [])

(*
 * normalizeConditionalsVisitor ensures that every if block has an
 * accompanying else block (by adding empty "else { }" blocks where
 * necessary).  It also attempts to convert conditional expressions
 * into predicates (i.e. binary expressions with one of the comparison
 * operators ==, !=, >, <, >=, <=.)
 *)
class normalizeConditionalsVisitor =

  let isCompareOp op =
    match op with
      | Eq -> true  | Ne -> true  | Lt -> true
      | Gt -> true  | Le -> true  | Ge -> true
      | _ -> false
  in

  let negateCompareOp op =
    match op with
      | Eq -> Ne  | Ne -> Eq
      | Lt -> Ge  | Ge -> Lt
      | Le -> Gt  | Gt -> Le
      | _ ->
          invalid_arg "negateCompareOp"
  in

  (* TODO(jburnim): We ignore casts here because downcasting can
   * convert a non-zero value into a zero -- e.g. from a larger to a
   * smaller integral type.  However, we could safely handle casting
   * from smaller to larger integral types. *)
  let rec mkPredicate e negated =
    match e with
      | UnOp (LNot, e, _) -> mkPredicate e (not negated)

      | BinOp (op, e1, e2, ty) when isCompareOp op ->
          if negated then
            BinOp (negateCompareOp op, e1, e2, ty)
          else
            e

      | _ ->
          let op = if negated then Eq else Ne in
            BinOp (op, e, zero, intType)
  in

object (self)
  inherit nopCilVisitor

  method vstmt(s) =
    match s.skind with
      | If (e, b1, b2, loc) ->
          (* Ensure neither branch is empty. *)
          if (b1.bstmts == []) then b1.bstmts <- [mkEmptyStmt ()] ;
          if (b2.bstmts == []) then b2.bstmts <- [mkEmptyStmt ()] ;
          (* Ensure the conditional is actually a predicate. *)
          (* s.skind <- If (mkPredicate e false, b1, b2, loc) ; *)
          DoChildren

      | _ -> DoChildren

end

let addressOf : lval -> exp = mkAddrOrStartOf

let hasAddress (_, off) =
  let rec containsBitField off =
    match off with
      | NoOffset         -> false
      | Field (fi, off) -> (isSome fi.fbitfield) || (containsBitField off)
      | Index (_, off)  -> containsBitField off
  in
    not (containsBitField off)
(* 
 * written by Hyunwoo Kim (17.07.13)
 * arguments, line and file name, were added to __CrownBranch function.
 *)
let lineArg = ("line", lineType,      [])
let fnameArg = ("fname", fnameType,   [])
let fname2Arg = ("fname2", fnameType,   [])
let idArg   = ("id",   idType,        [])
let bidArg  = ("bid",  bidType,       [])
let fidArg  = ("fid",  fidType,       [])
let valArg  = ("val",  valType,       [])
let valFpArg = ("fp_val", valFpType,  [])
let addrArg = ("addr", addrType,      [])
let opArg   = ("op",   opType,        [])
let boolArg = ("b",    boolType,      [])
let typeArg = ("type", typeType,      [])
let sizeArg () = ("size", !typeOfSizeOf, [])
let nameArg = ("name", charptrType, [])

let mkInstFunc f name args =
  let ty = TFun (voidType, Some (idArg :: args), false, []) in
  let func = findOrCreateFunc f ("__Crown" ^ name) ty in
    func.vstorage <- Extern ;
    func.vattr <- [Attr ("crown_skip", [])] ;
    func

let mkInstCall func args =
  let args' = integer (getNewId ()) :: args in
    Call (None, Lval (var func), args', locUnknown)

let toAddr e = CastE (addrType, e)
let toInt e = CastE (intType, e)

let toType ty =
  let tyCode =
    match (unrollType ty) with
      | TInt (IUChar,     _) ->  0
      | TInt (ISChar,     _) ->  1
      | TInt (IChar,      _) ->  1   (* we assume 'char' is signed *)
      | TInt (IUShort,    _) ->  2
      | TInt (IShort,     _) ->  3
      | TInt (IUInt,      _) ->  4
      | TInt (IInt,       _) ->  5
      | TInt (IULong,     _) ->  6
      | TInt (ILong,      _) ->  7
      | TInt (IULongLong, _) ->  8
      | TInt (ILongLong,  _) ->  9
      | TPtr _               ->  6
      | TEnum _              ->  5
      (* Arrays, structures, and unions are "aggregates". *)
      | TArray _             -> 10
      | TComp _              -> 10
      (* Support floating point. *)
      | TFloat (FFloat,  _)  -> 12
      | TFloat (FDouble, _)  -> 13
      (* va_list is a pointer *)
      | TBuiltin_va_list _ -> 6
      (* Other. *)
      | _ -> invalid_arg (Pretty.sprint 2 (d_type () ty))
  in
    integer tyCode

class crownInstrumentVisitor f =
  (*
   * Get handles to the instrumentation functions.
   *
   * NOTE: If the file we are instrumenting includes "crown.h", this
   * code will grab the varinfo's from the included declarations.
   * Otherwise, it will create declarations for these functions.
   *)
  let loadFunc         = mkInstFunc f "Load" [addrArg; typeArg; valArg; valFpArg;(* nameArg*)] in
  let storeFunc        = mkInstFunc f "Store" [addrArg] in
  let clearStackFunc   = mkInstFunc f "ClearStack" [] in
  let apply1Func       = mkInstFunc f "Apply1" [opArg; typeArg; valArg; valFpArg] in
  let apply2Func       = mkInstFunc f "Apply2" [opArg; typeArg; valArg; valFpArg] in
(*
 * written by Hyunwoo Kim (17.07.13)
 * arguments, line and file name, were added to __CrownBranch function.
 *)
  let branchFunc       = mkInstFunc f "Branch" [bidArg; boolArg; lineArg; fnameArg] in
  let callFunc         = mkInstFunc f "Call" [fidArg] in
  let returnFunc       = mkInstFunc f "Return" [] in
  let handleReturnFunc = mkInstFunc f "HandleReturn" [typeArg; valArg; valFpArg] in
  let setCallerCalleeNameFunc    = mkInstFunc f "SetCallerCalleeName" [fnameArg; fname2Arg] in
  let enableSymbolicFunc   = mkInstFunc f "EnableSymbolic" [fnameArg] in
  let checkSymbolicFunc = mkInstFunc f "CheckSymbolic" [fnameArg] in

  (*
   * Functions to create calls to the above instrumentation functions.
   *)
  let unaryOp op =
    let c =
      match op with
        | Neg -> 24  | BNot -> 25  |  LNot -> 26
    in
      integer c
  in

  let castOp signed =
    if signed then
      integer 28
    else
      integer 27
  in

  let binaryOp (signed, op) =
    let c =
      match (signed, op) with
        (* arithmetic ops *)
        | _, PlusA        ->  0  | _, MinusA      ->  1  | _, Mult       ->  2
        | false, Div      ->  3  | true, Div      ->  4
        | false, Mod      ->  5  | true, Mod      ->  6
        (* bitwise ops *)
        | _, Shiftlt      ->  7  | false, Shiftrt ->  8  | true, Shiftrt ->  9
        | _, BAnd         -> 10  | _, BOr         -> 11  | _, BXor       -> 12
        (* comparison ops *)
        | _, Eq           -> 13  | _, Ne          -> 14
        | false, Gt       -> 15  | true, Gt       -> 16
        | false, Le       -> 17  | true, Le       -> 18
        | false, Lt       -> 19  | true, Lt       -> 20
        | false, Ge       -> 21  | true, Ge       -> 22
        (* all that's left are logical ops, which we should never encounter *)
        | _ -> 23
    in
      integer c
  in
  let toValue e =
        CastE (valType, e)
  in
  let toFpValue e = 
        CastE (valFpType, e)
  in

  let toType ty =
    let tyCode =
      match (unrollType ty) with
        | TInt (IUChar,     _) ->  0
        | TInt (ISChar,     _) ->  1
        | TInt (IChar,      _) ->  1   (* we assume 'char' is signed *)
        | TInt (IUShort,    _) ->  2
        | TInt (IShort,     _) ->  3
        | TInt (IUInt,      _) ->  4
        | TInt (IInt,       _) ->  5
        | TInt (IULong,     _) ->  6
        | TInt (ILong,      _) ->  7
        | TInt (IULongLong, _) ->  8
        | TInt (ILongLong,  _) ->  9
        | TPtr _               ->  6
        | TEnum _              ->  5
        (* Arrays, structures, and unions are "aggregates". *)
        | TArray _             -> 10
        | TComp _              -> 10
        (* Support floating point. *)
        | TFloat (FFloat,  _)  -> 12
        | TFloat (FDouble, _)  -> 13
        | TFloat (FLongDouble, _) -> 14
        (* _Bool is treated as char*) 
        | TInt (IBool, _) -> 1
        (* va_list is a pointer *)
        | TBuiltin_va_list _ -> 6
        (* Other. *)
        | _ -> invalid_arg (Pretty.sprint 2 (d_type () ty))
    in
      integer tyCode
  in

  let loadVal ty v =
    if isSymbolicType ty then
      toValue v
    else
      sizeOf ty
  in
  let loadFpVal ty v = 
    if isSymbolicFpType ty then
      toFpValue v
    else
      sizeOf ty
  in

  let mkLoad addr ty v    = mkInstCall loadFunc [toAddr addr; toType ty; loadVal ty v; loadFpVal ty v; (* namearg *)] in
  let mkStore addr        = mkInstCall storeFunc [toAddr addr] in
  let mkClearStack ()     = mkInstCall clearStackFunc [] in
  let mkCast signed ty v  = mkInstCall apply1Func [castOp signed; toType ty; toValue v; loadFpVal ty v] in
  let mkApply1 op ty v    = mkInstCall apply1Func [unaryOp op; toType ty; toValue v; loadFpVal ty v] in
  let mkApply2 op ty v    = mkInstCall apply2Func [binaryOp op; toType ty; toValue v; loadFpVal ty v] in
  (* 
   * written by Hyunwoo Kim (17.07.13)
   * __LINE__ and __FILE__ directives were added as parameter of __CrownBranch function.
   *)
  let mkBranch bid b      = mkInstCall branchFunc [integer bid; integer b; mkString "__LINE__"; mkString "__FILE__"] in
  let mkCall fid          = mkInstCall callFunc [integer fid] in
  let mkReturn ()         = mkInstCall returnFunc [] in
  let mkHandleReturn ty v = mkInstCall handleReturnFunc [toType ty; loadVal ty v; loadFpVal ty v] in
  let mkSetCallerCalleeName caller callee = mkInstCall setCallerCalleeNameFunc [mkString caller; mkString callee] in
  let mkEnableSymbolic caller = mkInstCall enableSymbolicFunc [mkString caller] in
  let mkCheckSymbolic callee = mkInstCall checkSymbolicFunc [mkString callee] in

  (*
   * Instrument an expression.
   *)
  let rec instrumentExpr e =
	(* code for produce correct variable name...
		let rec printexpr expr =
			let rec printlval (lhost, offset) =
					let rec printOffset offs =
						match offs with
							|NoOffset -> ()
							|Field (finfo, off2) -> Printf.printf ".%s" finfo.fname; printOffset off2;()
							|Index (ex, off2) -> Printf.printf "["; printexpr ex; Printf.printf "]"; printOffset off2; ()
					in
					(match lhost with
						|Var varinfo ->
							Printf.printf "%s" varinfo.vname; printOffset offset; ()
						|Mem e ->
							Printf.printf "Mem ("; printexpr e; Printf.printf ")"; printOffset offset; ()
					)
			in
			match expr with
				|Const c ->
					(match c with
						|CInt64 (i, ik, st) ->
							Printf.printf "%s" (Int64.to_string i); ()
						|CStr s ->
							Printf.printf "\"%s\"" s; ()
						|CWStr l ->
							Printf.printf "CWStr";()
						|CChr c ->
							Printf.printf "\'%c\'" c; ()
						|CReal (f,k,st) ->
							Printf.printf "%f" f; ()
						|CEnum (e,s,en) ->
							Printf.printf "enum"; ()
					)
				|Lval (lhost, offset)-> printlval (lhost, offset);
				|SizeOf typ -> Printf.printf"Sizeof "; ()
				|SizeOfStr s ->
					Printf.printf "sizeofstr (%s)" s; ()
				|SizeOfE e ->
					Printf.printf "SizeOFE "; printexpr e; ()
				|AlignOf t ->
					Printf.printf "AlignOf "; ()
				|AlignOfE e ->
					Printf.printf "AlignOfE "; printexpr e; ()
				|UnOp (unop, e, ty) ->
					(match unop with
						|Neg -> Printf.printf " -("; printexpr e;Printf.printf ")"; ()
						|BNot -> Printf.printf " ~("; printexpr e; Printf.printf ")";()
						|LNot -> Printf.printf " !("; printexpr e; Printf.printf ")"; ()
					)
				|BinOp (binop,e1,e2,typ) ->
					let getStrbinop binop =
						match binop with
							|PlusA -> "+"	|PlusPI -> "+"	|IndexPI -> "i+" |MinusA -> "-"	|MinusPI -> "-"
							|MinusPP -> "-" |Mult -> "*"|Div -> "\\"	|Mod -> "%" |Shiftlt -> "shiftleft"
							|Shiftrt -> "shiftright" |Lt -> "<" |Gt -> ">" |Le -> "<=" |Ge -> ">="
							|Eq -> "==" |Ne -> "!=" |BAnd -> "&" |BXor -> "exclusive-or" |BOr -> "|"
							|LAnd -> "&&" |LOr -> "||"
					in
					Printf.printf "binop {"; printexpr e1; Printf.printf " %s " (getStrbinop binop); printexpr e2; Printf.printf "}"; ()
				|CastE (typ, e) ->
					Printf.printf "CastE ("; printexpr e; Printf.printf " )";()
				|AddrOf lv ->
					Printf.printf "AddrOf ("; printlval lv; Printf.printf " )"; ()
				|StartOf lv ->
					Printf.printf "StartOf ("; printlval lv; Printf.printf " )"; ()
				|_ ->
					Printf.printf "call etc.."; ()
		in
		printexpr e;
		Printf.printf "\n";
		
		let constToStr e =
			match e with
				|Const (c) -> 
					match c with
						|CInt64 (i64, _, _) -> Int64.to_string i64
						|CStr (str) -> str
						|CWStr (li) -> "list"
						|CChr (ch) -> ch
						|CReal (f, _,_) -> string_of_float f
						|CEnum (_,_,_) -> "enum"
				|_ -> ""
		in*)
    let ty = typeOf e in
    if isConstant e then
      [mkLoad noAddr ty e (*(constToStr e)*)]
    else
      match e with
        | Lval lv when hasAddress lv ->
              [mkLoad (addressOf lv) ty e]

        | UnOp (op, e', _) ->
            (* Should skip this if we don't currently handle 'op'? *)
            (instrumentExpr e') @ [mkApply1 op ty e]

        | BinOp (op, e1, e2, _) ->
            (* Should skip this if we don't currently handle 'op'? *)
            let signed = isSignedType (typeOf e1) in
              (instrumentExpr e1)
              @ (instrumentExpr e2)
              @ [mkApply2 (signed, op) ty e]

        | CastE (_, e') when isStructureType ty ->
            (* Structure casts are meaningless -- just adding or
               removing const modifiers -- so skip. *)
            instrumentExpr e'

        | CastE (_, e') ->
            let signed = isSignedType (typeOf e') in
              (instrumentExpr e') @ [mkCast signed ty e]

        (* Default case: sizeof() and __alignof__() expressions. *)
        | _ -> [mkLoad noAddr ty e]
  in

object (self)
  inherit nopCilVisitor
  val mutable curFunc = emptyFunction "__empty__"
  (*
   * Instrument a statement (branch or function return).
   *)
  method vstmt(s) =
    match s.skind with
      | If (e, b1, b2, _) ->
          let getFirstStmtId blk = (List.hd blk.bstmts).sid in
          let b1_sid = getFirstStmtId b1 in
          let b2_sid = getFirstStmtId b2 in
            (self#queueInstr (instrumentExpr e) ;
              prependToBlock [mkBranch b1_sid 1] b1 ;
               prependToBlock [mkBranch b2_sid 0] b2 ;
             addBranchPair (b1_sid, b2_sid)) ;
          DoChildren 

      | Return (Some e, _) ->
          if isSymbolicType (typeOf e) then
            self#queueInstr (instrumentExpr e) ;
          self#queueInstr [mkReturn ()] ;
          SkipChildren

      | Return (None, _) ->
          self#queueInstr [mkReturn ()] ;
          SkipChildren

      | _ -> DoChildren

  (*
   * Instrument assignment and call statements.
   *)
  method vinst(i) =
      match i with
      | Set (lv, e, loc) when (true && hasAddress lv)(*type is ok, lv has addr *) ->
        (* If lv is an aggregate, it must be a struct/union. *)
            (self#queueInstr (instrumentExpr e) ;
             self#queueInstr [mkStore (addressOf lv)] ;
             SkipChildren)
          
      (* Don't instrument calls to functions marked as uninstrumented
       * except caller-callee name setting. *)
      | Call (ret, Lval (Var f, NoOffset), _, _)
          when shouldSkipFunction f -> 
              if ((isProbeFunction f) == false)
              then
                  ChangeTo [mkSetCallerCalleeName curFunc.svar.vname f.vname;
                  i; mkEnableSymbolic curFunc.svar.vname;]
              else SkipChildren

      | Call (ret, Lval (Var f, NoOffset), args, loc) ->
         let isSymbolicExp e = isSymbolicType (typeOf e) in
         let isSymbolicLval lv = isSymbolicType (typeOfLval lv) in
         let argsToInst = List.filter isSymbolicExp args in
           self#queueInstr (concatMap instrumentExpr argsToInst) ;
           self#queueInstr [mkSetCallerCalleeName curFunc.svar.vname f.vname];
         (match ret with
            | Some lv when ((isSymbolicLval lv) && (hasAddress lv)) ->
              ChangeTo [i ; mkEnableSymbolic curFunc.svar.vname;
                        mkHandleReturn (typeOfLval lv) (Lval lv) ;
                        mkStore (addressOf lv)]
            | _ -> ChangeTo [i ; mkEnableSymbolic curFunc.svar.vname; mkClearStack ()])
       | _ -> DoChildren

  (*
   * Instrument function entry.
   *)
  method vfunc(f) =
      (*Printf.printf "Instr. func: %s\n" f.svar.vname;
      Printf.printf "Line: %d\n" f.svar.vdecl.line;
      Printf.printf "Inline: %B\n" f.svar.vinline;*)
      let skip = shouldSkipFunction f.svar in
      (*Printf.printf "Skip: %B\n" skip;*)
      curFunc <- f;
    if shouldSkipFunction f.svar then
      SkipChildren
    else
      let instParam v = mkStore (addressOf (var v)) in
      let isSymbolic v = isSymbolicType v.vtype in
      let (_, _, isVarArgs, _) = splitFunctionType f.svar.vtype in
      let paramsToInst = List.filter isSymbolic f.sformals in
        addFunction () ;
        (* 
         * skip instrumenting parameters of main because
         * CROWN initialization is not yet performed
         *)
        if ((not isVarArgs) && (0 != String.compare f.svar.vname "main")) then
            prependToBlock (List.rev_map instParam paramsToInst) f.sbody
         else
           prependToBlock [mkClearStack ()] f.sbody;
        prependToBlock [mkCall !funCount] f.sbody ;
        prependToBlock [mkCheckSymbolic f.svar.vname] f.sbody ;
        DoChildren

  method vglob(g) =
    match g with
      |GCompTag (compinfo, loc) ->
        let remove field = field.fbitfield <- None in
        List.iter remove compinfo.cfields;
        DoChildren
      |_ -> DoChildren


end
let addCrownInitializer f =
  let crownInitFunc = mkInstFunc f "Init" [] in
  let globalInit = getGlobInit f in
    crownInitFunc.vstorage <- Extern ;
    crownInitFunc.vattr <- [Attr ("crown_skip", [])] ;
    prependToBlock [mkInstCall crownInitFunc []] globalInit.sbody

let prepareGlobalForCFG glob =
  match glob with
    | GFun(func, _) -> prepareCFG func
    | _ -> ()

let feature : featureDescr =
  { fd_name = "CrownInstrument";
    fd_enabled = ref false;
    fd_description = "instrument a program for use with CROWN";
    fd_extraopt = [];
    fd_post_check = true;
    fd_doit =
      function (f: file) ->
        ((* Simplify the code:
          *  - simplifying expressions with complex memory references
          *  - converting loops and switches into goto's and if's
          *  - transforming functions to have exactly one return *)
          Simplemem.feature.fd_doit f ;
          iterGlobals f prepareGlobalForCFG ;
          Oneret.feature.fd_doit f ;
          (* To simplify later processing:
           *  - ensure that every 'if' has a non-empty else block
           *  - try to transform conditional expressions into predicates
           *    (e.g. "if (!x) {}" to "if (x == 0) {}") *)
          (let ncVisitor = new normalizeConditionalsVisitor in
             visitCilFileSameGlobals (ncVisitor :> cilVisitor) f) ;
          (* Clear out any existing CFG information. *)
          Cfg.clearFileCFG f ;
          (* Read the ID and statement counts from files.  (This must
           * occur after clearFileCFG, because clearFileCfg clobbers
           * the statement counter.) *)
          readIdCount () ;
          readStmtCount () ;
          readFunCount () ;
          (* Compute the control-flow graph. *)
          Cfg.computeFileCFG f ;
          (* Adds function calls to the CFG, by building a map from
           * function names to the first statements in those functions
           * and by explicitly adding edges for calls to functions
           * defined in this file. *)
          handleCallEdgesAndWriteCfg f ;
  
          (* Finally instrument the program. *)
    (let instVisitor = new crownInstrumentVisitor f in
             visitCilFileSameGlobals (instVisitor :> cilVisitor) f) ;
          (* Add a function to initialize the instrumentation library. *)
             if (!isMainInFile) then addCrownInitializer f ; 
          (* Write the ID and statement counts, the branches. *)
          writeIdCount () ;
          writeStmtCount () ;
          writeFunCount () ;
          writeBranches ());
  }
