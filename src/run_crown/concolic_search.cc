// Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
//
// This file is part of CROWN, which is distributed under the revised
// BSD license.  A copy of this license can be found in the file LICENSE.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
// for details.

#include <algorithm>
#include <assert.h>
#include <cmath>
#include <fstream>
#include <functional>
#include <limits>
#include <iostream>
#include <stdio.h>
#include <stdlib.h>
#include <queue>
#include <utility>
#include <sys/resource.h>
#include <sys/stat.h>
#include <unistd.h>
#include <string.h>

#include "run_crown/z3_solver.h"
#include "run_crown/concolic_search.h"
#include "base/basic_types.h"
#include "base/basic_functions.h"
#include "run_crown/unary_expression.h"

//#include "run_crown/symbolic_expression_factory.h"
#define FILE2SHOW_ASSUME_VIOLATED "__SYM_assume_violated"

using std::binary_function;
using std::ifstream;
using std::ios;
using std::min;
using std::max;
using std::numeric_limits;
using std::pair;
using std::queue;
using std::random_shuffle;
using std::stable_sort;
size_t crown::Z3Solver::no_reduction_sat_count = 0;
size_t crown::Z3Solver::no_reduction_unsat_count = 0;
unsigned long long crown::Z3Solver::no_reduction_sat_formula_length = 0;
unsigned long long crown::Z3Solver::no_reduction_unsat_formula_length = 0;

/* TCdir (defined in crown-fp/src/run_crown.cc) is a relative directory path 
 * to save generated test cases files * (i.e. input.1, input.2, ...)
 * TCdir is empty if -TCDIR commandline option is not used.
 * 2017.07.07 Hyunwoo Kim 
 */
extern string TCdir;
extern int flag_init_TC;

namespace crown {

namespace {

typedef pair<size_t,int> ScoredBranch;

struct ScoredBranchComp
	: public binary_function<ScoredBranch, ScoredBranch, bool> {
	bool operator()(const ScoredBranch& a, const ScoredBranch& b) const {
		return (a.second < b.second);
	}
};

// A flag to show if SYM_assume(exp) is violated;
bool SYM_assume_violated;

}  // namespace


////////////////////////////////////////////////////////////////////////
//// Search ////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

Search::Search(const string& program, int max_iterations)
  : sym_path_length(0), con_path_length(0),
    program_(program), max_iters_(max_iterations), num_iters_(0){

	start_time_ = time(NULL);

	{ // Read in the set of branches.
		max_branch_ = 0;
		max_function_ = 0;
		branches_.reserve(100000);
		branch_count_.reserve(100000);
		branch_count_.push_back(0);

		ifstream in("branches");
		assert(in);
		function_id_t fid;
		int numBranches;
		while (in >> fid >> numBranches) {
			branch_count_.push_back(2 * numBranches);
			branch_id_t b1, b2;
			for (int i = 0; i < numBranches; i++) {
				assert(in >> b1 >> b2);
				branches_.push_back(b1);
				branches_.push_back(b2);
				max_branch_ = max(max_branch_, max(b1, b2));
			}
		}
		in.close();
		max_branch_ ++;
		max_function_ = branch_count_.size();
	}


	// Compute the paired-branch map.
	paired_branch_.resize(max_branch_);
	for (size_t i = 0; i < branches_.size(); i += 2) {
		paired_branch_[branches_[i]] = branches_[i+1];
		paired_branch_[branches_[i+1]] = branches_[i];
	}

	// Compute the branch-to-function map.
	branch_function_.resize(max_branch_);
	{ size_t i = 0;
		for (function_id_t j = 0; j < branch_count_.size(); j++) {
			for (size_t k = 0; k < branch_count_[j]; k++) {
				branch_function_[branches_[i++]] = j;
			}
		}
	}


	// Initialize all branches to "uncovered" (and functions to "unreached").
	total_num_covered_ = num_covered_ = 0;
	reachable_functions_ = reachable_branches_ = 0;
	covered_.resize(max_branch_, false);
	total_covered_.resize(max_branch_, false);
	reached_.resize(max_function_, false);

#if 0
	{ // Read in any previous coverage (for faster debugging).
		ifstream in("coverage");
		branch_id_t bid;
		while (in >> bid) {
			covered_[bid] = true;
			num_covered_ ++;
			if (!reached_[branch_function_[bid]]) {
				reached_[branch_function_[bid]] = true;
				reachable_functions_ ++;
				reachable_branches_ += branch_count_[branch_function_[bid]];
			}
		}

		total_num_covered_ = 0;
		total_covered_ = covered_;
	}
#endif

	// Print out the initial coverage.
	//  fprintf(stderr, "Iteration 0 (0s): covered %u branches [%u reach funs, %u reach branches].\n",
	//          num_covered_, reachable_functions_, reachable_branches_);

	// Sort the branches.
	sort(branches_.begin(), branches_.end());
	}


Search::~Search() {

#if 0
	fprintf(stderr, "Path count: %u\n", Z3Solver::path_cnt_);
	fprintf(stderr, "Sum of paths' lengths: %u fomulas\n", Z3Solver::path_sum_);
	fprintf(stderr, "Solving Time: %lf s\n", Z3Solver::solving_time_);
	fprintf(stderr, "Reduction SAT count: %u\n", Z3Solver::reduction_sat_count);
	fprintf(stderr, "Reduction UNSAT count: %u\n", Z3Solver::reduction_unsat_count);
	fprintf(stderr, "Reduction SAT length(avg): %lf\n",
			(double)Z3Solver::reduction_sat_formula_length/Z3Solver::reduction_sat_count);
	fprintf(stderr, "Reduction UNSAT length(avg): %lf\n",
			(double)Z3Solver::reduction_unsat_formula_length/Z3Solver::reduction_unsat_count);

	fprintf(stderr, "No Reduction SAT count: %u\n", Z3Solver::no_reduction_sat_count);
	fprintf(stderr, "No Reduction UNSAT count: %u\n", Z3Solver::no_reduction_unsat_count);
	fprintf(stderr, "No Reduction SAT length(avg): %lf\n",
			(double)Z3Solver::no_reduction_sat_formula_length/Z3Solver::no_reduction_sat_count);
	fprintf(stderr, "No Reduction UNSAT length(avg): %lf\n",
			(double)Z3Solver::no_reduction_unsat_formula_length/Z3Solver::no_reduction_unsat_count);
	fprintf(stderr, "Symbolic path length(avg): %lf\n", (double)sym_path_length/(double)num_iters_);
	fprintf(stderr, "Concrete path length(avg): %lf\n", (double)con_path_length/(double)num_iters_);
	struct rusage self_usage, child_usage;
	struct timeval total_stime, total_utime;
	int carry;

	getrusage(RUSAGE_SELF, &self_usage);
	getrusage(RUSAGE_CHILDREN, &child_usage);
	carry = (self_usage.ru_stime.tv_usec + child_usage.ru_stime.tv_usec) / (1000 * 1000);
	total_stime.tv_usec = (self_usage.ru_stime.tv_usec + child_usage.ru_stime.tv_usec) % (1000 * 1000);
	total_stime.tv_sec = (self_usage.ru_stime.tv_sec + child_usage.ru_stime.tv_sec) + carry;
	carry = (self_usage.ru_stime.tv_usec + child_usage.ru_stime.tv_usec) / (1000 * 1000);
	total_utime.tv_usec = (self_usage.ru_utime.tv_usec + child_usage.ru_utime.tv_usec) % (1000 * 1000);
	total_utime.tv_sec = (self_usage.ru_utime.tv_sec + child_usage.ru_utime.tv_sec) + carry;

	fprintf(stderr, "CROWN: Sys %ld.%lds User %ld.%ld\n",
			self_usage.ru_stime.tv_sec, self_usage.ru_stime.tv_usec/1000,
			self_usage.ru_utime.tv_sec, self_usage.ru_utime.tv_usec/1000);
	fprintf(stderr, "Target: Sys %ld.%lds User %ld.%ld\n",
			child_usage.ru_stime.tv_sec, child_usage.ru_stime.tv_usec/1000,
			child_usage.ru_utime.tv_sec, child_usage.ru_utime.tv_usec/1000);
	fprintf(stderr, "Total: Sys %ld.%lds User %ld.%ld\n",
			total_stime.tv_sec, total_stime.tv_usec/1000,
			total_utime.tv_sec, total_utime.tv_usec/1000);
#endif
}


void Search::WriteInputToFileOrDie(const string& file,
		const vector<Value_t>& input, const vector<unsigned char>& h, const vector<unsigned char>& l, const vector<unsigned char>& idx) {
	FILE* f = fopen(file.c_str(), "w");
	if (!f) {
		fprintf(stderr, "Failed to open %s.\n", file.c_str());
		perror("Error: ");
		exit(-1);
	}

	for (size_t i = 0; i < input.size(); i++) {
#ifdef DEBUG
		std::cerr<<"Next Input value: "<<input[i].integral <<" "<<input[i].floating<<" "<<input[i].type <<std::endl;
#endif
		if((int) h[i] == 0){
			fprintf(f, "%d\n",(int)input[i].type);
		} else {
			fprintf(f, "%d %d %d %d\n", (int)input[i].type, (int) h[i], (int) l[i], (int) idx[i]);
		}
		if(input[i].type == types::FLOAT){
			fwrite(crown::floatToBinString((float)input[i].floating)->c_str(),
					sizeof(char), sizeof(float)*8, f);
			fprintf(f, "\n");
		}else if(input[i].type == types::DOUBLE){
			fwrite(crown::doubleToBinString((double)input[i].floating)->c_str(),
					sizeof(char), sizeof(double)*8, f);
			fprintf(f, "\n");
		}else{
			fprintf(f, "%lld\n", input[i].integral);
		}
	}

	fclose(f);
}


void Search::WriteCoverageToFileOrDie(const string& file) {
	FILE* f = fopen(file.c_str(), "w");
	if (!f) {
		fprintf(stderr, "Failed to open %s.\n", file.c_str());
		perror("Error: ");
		exit(-1);
	}

	for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
		if (total_covered_[*i]) {
			fprintf(f, "%d\n", *i);
		}
	}

	fclose(f);
}


int Search::LaunchProgram(const vector<Value_t>& inputs) {
    int ret;
	vector<unsigned char> tmph = vector<unsigned char>();
	vector<unsigned char> tmpl = vector<unsigned char>();
	vector<unsigned char> tmpi = vector<unsigned char>();
	tmph.resize(inputs.size());
	tmpl.resize(inputs.size());
	tmpi.resize(inputs.size());
	const vector<unsigned char>& h = tmph;
	const vector<unsigned char>& l = tmpl;
	const vector<unsigned char>& i = tmpi;

	if(flag_init_TC == 1)
		flag_init_TC = 0;
	else
		WriteInputToFileOrDie("input", inputs, h, l,i);
	// The current directory must have "input" file
	ret = system(program_.c_str()); 
    return ret;
}



void Search::RunProgram(const vector<Value_t>& inputs, SymbolicExecution* ex) {
    int exitcode;
	fprintf(stderr, "-------------------------\n");


	if (++num_iters_ > max_iters_) {
#if 0
		fprintf(stderr, "Path count: %u\n", Z3Solver::path_cnt_);
		fprintf(stderr, "Sum of paths' lengths: %u fomulas\n", Z3Solver::path_sum_);
		fprintf(stderr, "Solving Time: %lf s\n", Z3Solver::solving_time_);

		struct rusage self_usage, child_usage;
		struct timeval total_stime, total_utime;
		int carry;

		getrusage(RUSAGE_SELF, &self_usage);
		getrusage(RUSAGE_CHILDREN, &child_usage);
		carry = (self_usage.ru_stime.tv_usec + child_usage.ru_stime.tv_usec) / (1000 * 1000);
		total_stime.tv_usec = (self_usage.ru_stime.tv_usec + child_usage.ru_stime.tv_usec) % (1000 * 1000);
		total_stime.tv_sec = (self_usage.ru_stime.tv_sec + child_usage.ru_stime.tv_sec) + carry;
		carry = (self_usage.ru_stime.tv_usec + child_usage.ru_stime.tv_usec) / (1000 * 1000);
		total_utime.tv_usec = (self_usage.ru_utime.tv_usec + child_usage.ru_utime.tv_usec) % (1000 * 1000);
		total_utime.tv_sec = (self_usage.ru_utime.tv_sec + child_usage.ru_utime.tv_sec) + carry;

		fprintf(stderr, "CROWN: Sys %ld.%lds User %ld.%ld\n",
				self_usage.ru_stime.tv_sec, self_usage.ru_stime.tv_usec/1000,
				self_usage.ru_utime.tv_sec, self_usage.ru_utime.tv_usec/1000);
		fprintf(stderr, "Target: Sys %ld.%lds User %ld.%ld\n",
				child_usage.ru_stime.tv_sec, child_usage.ru_stime.tv_usec/1000,
				child_usage.ru_utime.tv_sec, child_usage.ru_utime.tv_usec/1000);
		fprintf(stderr, "Total: Sys %ld.%lds User %ld.%ld\n",
				total_stime.tv_sec, total_stime.tv_usec/1000,
				total_utime.tv_sec, total_utime.tv_usec/1000);
#endif
		// TODO(jburnim): Devise a better system for capping the iterations.
		exit(0);
	}

	// Run the program.
	exitcode = LaunchProgram(inputs);



	// Read the execution from the program.
	// Want to do this with sockets.  (Currently doing it with files.)
	ifstream in("szd_execution", ios::in | ios::binary);
	global_tracker_ = NULL;
	global_numOfExpr_ = 0;
	global_numOfVar_ = 0;
	global_numOfOperator_ = 0;
	assert(in && ex->Parse(in));
	//std::cout<<"Parse time "<<((double)clock() - clk)/CLOCKS_PER_SEC<<" numOfExpr "<<global_numOfExpr_<<" op "<<global_numOfOperator_<<" var "<<global_numOfVar_<<std::endl;
	in.close();

	/* Moonzoo Kim (2018-11-10)
	 * 
	 * If a child process that runs a target program has violated SYM_assume,
	 * the child process creates a file FILE2SHOW_ASSUME_VIOLATED.
	 * 
	 * run_crown checks if the file exists and if so, 
	 * it updates SYM_assume_violated as true.
	 * if SYM_assume_violated is true, 
	 * 1. run_crown removes * the current test input and the flag file here, and
	 * 2. all search strategies do not update coverage except cfg heuristics
	 *    (i.e., if(!SYM_assume_violate) UpdateCoverage(...).)
	 *
	 * NOTE: ex->Parse(in) should be executed to continue next iteration 
	 * regardless of SYM_assume violation.
	 */
	FILE *f=fopen(FILE2SHOW_ASSUME_VIOLATED, "r");
	SYM_assume_violated = f !=NULL ? true: false; 
	if(f != NULL && fclose(f)) {
		fprintf(stderr,"Error: %s is not closed\n", FILE2SHOW_ASSUME_VIOLATED);
	}

	if (SYM_assume_violated) {
		num_iters_ -= 1;
		if(remove(FILE2SHOW_ASSUME_VIOLATED)!=0) {
			printf("Error: %s cannot be removed!!!\n",FILE2SHOW_ASSUME_VIOLATED);
		}
		return;
	} 

	sym_path_length += ex->path().constraints().size();
	con_path_length += ex->path().branches().size();

	/* This part saves test case files in TCdir if TCdir is not empty.
	 * Note 1. if the directory pointed by TCdir already exists,
	 *         test cases files are not saved.
	 * Note 2. The length of path should be shorter than BUFSIZ (>255).
	 * 2017.07.07 Hyunwoo Kim
	 *
	 * Moved the input.<N> generation code to the end of RunProgram().
	 * (Originally, this code was at the start of LaunchProgram()
	 *  to generate input.<N> before the iteration)
	 * 2017.07.29 Woong-gyu Yang
	 */
	if (!TCdir.empty())
	{
		static int status = -1;
		static bool is_mkdir_called = false;
		if (!is_mkdir_called)
		{
			status = mkdir(TCdir.c_str(),
					S_IRWXU | S_IRWXG | S_IROTH | S_IXOTH);
			is_mkdir_called = true;
			if (status == -1)
			{
				fprintf(stderr,
						"Error: can't create testcase directory %s "
						"and testcase files\n",
						TCdir.c_str());
			}
		}

		if (status != -1)
		{
			char fname[BUFSIZ] = {0,};
			snprintf(fname, BUFSIZ, "%s/input.%d", TCdir.c_str(), num_iters_);

			if (WIFEXITED(exitcode) != 0){
				WriteInputToFileOrDie(fname, ex->inputs(), ex->h(), ex->l(), ex->indexSize());
			}else{
				WriteInputToFileOrDie(fname,       inputs, ex->h(), ex->l(), ex->indexSize());
			}
		}
	}
}


bool Search::UpdateCoverage(const SymbolicExecution& ex) {
	return UpdateCoverage(ex, NULL);
}

bool Search::UpdateCoverage(const SymbolicExecution& ex,
		set<branch_id_t>* new_branches) {

	const unsigned int prev_covered_ = num_covered_;
	const SymbolicPath &path = ex.path();
	const vector<branch_id_t>& branches = path.branches();


	for (BranchIt i = branches.begin(); i != branches.end(); ++i) {
		if ((*i > 0) && !covered_[*i]) {
			covered_[*i] = true;
			num_covered_++;
			if (new_branches) {
				new_branches->insert(*i);
			}
			if (!reached_[branch_function_[*i]]) {
				reached_[branch_function_[*i]] = true;
				reachable_functions_ ++;
				reachable_branches_ += branch_count_[branch_function_[*i]];
			}
		}
		if ((*i > 0) && !total_covered_[*i]) {
			total_covered_[*i] = true;
			total_num_covered_++;
		}
	}
	fprintf(stderr, "Iteration %d (%lds, %ld.%lds): covered %u branches [%u reach funs, %u reach branches].(%u, %u)\n",
			num_iters_, time(NULL)-start_time_, Z3Solver::GetRunningTime() / 1000, Z3Solver::GetRunningTime() % 1000,
			total_num_covered_, reachable_functions_, reachable_branches_, num_covered_, prev_covered_);
#if 0
	{
		fprintf(stderr, "Reduction SAT count: %u, ", Z3Solver::reduction_sat_count);
		fprintf(stderr, "Reduction UNSAT count: %u\n", Z3Solver::reduction_unsat_count);
		fprintf(stderr, "Reduction SAT length(avg): %lf, ",
				(double)Z3Solver::reduction_sat_formula_length/Z3Solver::reduction_sat_count);
		fprintf(stderr, "Reduction UNSAT length(avg): %lf\n",
				(double)Z3Solver::reduction_unsat_formula_length/Z3Solver::reduction_unsat_count);

		fprintf(stderr, "No Reduction SAT count: %u, ", Z3Solver::no_reduction_sat_count);
		fprintf(stderr, "No Reduction UNSAT count: %u\n", Z3Solver::no_reduction_unsat_count);
		fprintf(stderr, "No Reduction SAT length(avg): %lf, ",
				(double)Z3Solver::no_reduction_sat_formula_length/Z3Solver::no_reduction_sat_count);
		fprintf(stderr, "No Reduction UNSAT length(avg): %lf\n",
				(double)Z3Solver::no_reduction_unsat_formula_length/Z3Solver::no_reduction_unsat_count);
		fprintf(stderr, "Symbolic path length(avg): %lf, ", (double)sym_path_length/(double)num_iters_);
		fprintf(stderr, "Concrete path length(avg): %lf\n", (double)con_path_length/(double)num_iters_);
		struct rusage self_usage, child_usage;
		struct timeval total_stime, total_utime;
		int carry;

		getrusage(RUSAGE_SELF, &self_usage);
		getrusage(RUSAGE_CHILDREN, &child_usage);
		carry = (self_usage.ru_stime.tv_usec + child_usage.ru_stime.tv_usec) / (1000 * 1000);
		total_stime.tv_usec = (self_usage.ru_stime.tv_usec + child_usage.ru_stime.tv_usec) % (1000 * 1000);
		total_stime.tv_sec = (self_usage.ru_stime.tv_sec + child_usage.ru_stime.tv_sec) + carry;
		carry = (self_usage.ru_stime.tv_usec + child_usage.ru_stime.tv_usec) / (1000 * 1000);
		total_utime.tv_usec = (self_usage.ru_utime.tv_usec + child_usage.ru_utime.tv_usec) % (1000 * 1000);
		total_utime.tv_sec = (self_usage.ru_utime.tv_sec + child_usage.ru_utime.tv_sec) + carry;

		fprintf(stderr, "CROWN: Sys %ld.%lds User %ld.%ld\n",
				self_usage.ru_stime.tv_sec, self_usage.ru_stime.tv_usec/1000,
				self_usage.ru_utime.tv_sec, self_usage.ru_utime.tv_usec/1000);
		fprintf(stderr, "Target: Sys %ld.%lds User %ld.%ld\n",
				child_usage.ru_stime.tv_sec, child_usage.ru_stime.tv_usec/1000,
				child_usage.ru_utime.tv_sec, child_usage.ru_utime.tv_usec/1000);
		fprintf(stderr, "Total: Sys %ld.%lds User %ld.%ld\n",
				total_stime.tv_sec, total_stime.tv_usec/1000,
				total_utime.tv_sec, total_utime.tv_usec/1000);

	}
#endif
	bool found_new_branch = (num_covered_ > prev_covered_);
	if (found_new_branch) {
		WriteCoverageToFileOrDie("coverage");
	}

	return found_new_branch;
}


void Search::RandomInput(const map<var_t,type_t>& vars, vector<Value_t>* input) {
	input->resize(vars.size());

	for (map<var_t,type_t>::const_iterator it = vars.begin(); it != vars.end(); ++it) {
		Value_t val;
		val.type = it->second;
		for (size_t j = 0; j < 8; j++){
			val.integral = (val.integral << 8) + (rand() / 256);
		}
		val.floating = *reinterpret_cast<double*>(&val.integral);

		switch (it->second) {
			case types::U_CHAR:
				val.integral = (unsigned char)val.integral; break;
			case types::CHAR:
				val.integral = (char)val.integral; break;
			case types::U_SHORT:
				val.integral = (unsigned short)val.integral;break;
			case types::SHORT:
				val.integral = (short)val.integral;break;
			case types::U_INT:
				val.integral = (unsigned int)val.integral;break;
			case types::INT:
				val.integral = (int)val.integral;break;
			case types::U_LONG:
				val.integral = (unsigned long)val.integral;break;
			case types::LONG:
				val.integral = (long)val.integral;break;
			case types::U_LONG_LONG:
				val.integral = (unsigned long long)val.integral;break;
			case types::LONG_LONG:
				val.integral = (long long)val.integral;break;
			case types::FLOAT:
				val.floating = (float)val.floating; break;
			case types::DOUBLE:
				val.floating = (double)val.floating; break;
			case types::LONG_DOUBLE:
				val.floating = (long double)val.floating; break;
			case types::POINTER:
			case types::BOOLEAN:
				// ???
			case types::STRUCT:
				// ???
			default :
				val.integral = (unsigned char) val.integral;
				break;

		}
		input->at(it->first) = val;
	}
}


bool Search::SolveAtBranch(SymbolicExecution& ex,
		size_t branch_idx,
		vector<Value_t>* input) {
	global_tracker_ = ex.object_tracker();
	const vector<SymbolicExpr*>& constraints = ex.path().constraints();

	// Optimization: If any of the previous constraints are idential to the
	// branch_idx-th constraint, immediately return false.
	// Commenting out for time-being
/*
	for (int i = static_cast<int>(branch_idx) - 1; i >= 0; i--) {
		if (constraints[branch_idx]->Equals(*constraints[i]))
			return false;
	}
*/
	vector<const SymbolicExpr*> cs(constraints.begin(),
			constraints.begin()+branch_idx+1);
	map<var_t,Value_t> soln;
	//constraints[branch_idx]->Negate();
	SymbolicExpr *tempExpr = constraints[branch_idx];
	Value_t tempVal = Value_t(1 - tempExpr->value().integral, (double) (1 - tempExpr->value().floating), tempExpr->value().type);
	cs[branch_idx] = new UnaryExpr(ops::LOGICAL_NOT, tempExpr, kSizeOfType[tempVal.type], tempVal);
//SymbolicExprFactory::NewUnaryExpr(tempVal, ops::LOGICAL_NOT, tempExpr);

#ifdef DEBUG
	for (size_t i = 0; i < ex.inputs().size(); i++) {
		std::cerr << "(= x" << i << " " << ex.inputs()[i].integral << " "<<ex.inputs()[i].floating<<" "<<ex.inputs()[i].type<<" )"<<std::endl;
	}
#endif

	//TODO: Implement IncrementalSolve
	bool success = Z3Solver::Solve(ex.vars(),ex.values(),ex.h(), ex.l(), ex.exprs(), cs, &soln);
	//bool success = Z3Solver::IncrementalSolve(ex.inputs(), ex.vars(), cs, &soln);
	//constraints[branch_idx]->Negate();

//printf("ex tracker %d\n", ex.object_tracker2()->snapshotManager().size());
	//Init isCreateAST
	size_t managerSize = global_tracker_->astManager().size();
	for(size_t iter = 0; iter < managerSize; iter++){
		size_t objSize = global_tracker_->astManager()[iter]->size();
		for(size_t iter2 = 0; iter2 < objSize; iter2++){
			global_tracker_->isCreateAST()[iter]->at(iter2) = false;
		}
	}

	if (success) {
		// Merge the solution with the previous input to get the next
		// input.  (Could merge with random inputs, instead.)
		*input = ex.inputs();
		// RandomInput(ex.vars(), input);

		typedef map<var_t,Value_t>::const_iterator SolnIt;
		for (SolnIt i = soln.begin(); i != soln.end(); ++i) {
			(*input)[i->first] = i->second;
		}
		return true;
	}

	return false;
}

#if 0
bool Search::CheckPrediction(const SymbolicExecution& old_ex,
		const SymbolicExecution& new_ex,
		size_t branch_idx) {
	if ((old_ex.path().branches().size() <= branch_idx)
			|| (new_ex.path().branches().size() <= branch_idx)) {
		fprintf(stderr, "Size of branch is too small\n");
		return false;
	}

	for (size_t j = 0; j < branch_idx; j++) {
		if  (new_ex.path().branches()[j] != old_ex.path().branches()[j]) {
			fprintf(stderr, "Expected branch to take is %d but %d is executed in the middle of execution\n",
					old_ex.path().branches()[j], new_ex.path().branches()[j]);

			return false;
		}
	}
	if (new_ex.path().branches()[branch_idx]
			== paired_branch_[old_ex.path().branches()[branch_idx]]){
		return true;
	}else{
		fprintf(stderr, "Expected branch to take is %d but %d is executed at the flipping point\n",
				paired_branch_[old_ex.path().branches()[branch_idx]],
				new_ex.path().branches()[branch_idx]);
		return false;
	}
#endif

#if 1
bool Search::CheckPrediction(const SymbolicExecution& old_ex,
					const SymbolicExecution& new_ex,
					size_t branch_idx) {

	if ((old_ex.path().branches().size() <= branch_idx)
			|| (new_ex.path().branches().size() <= branch_idx)) {
		return false;
	}

	for (size_t j = 0; j < branch_idx; j++) {
		if  (new_ex.path().branches()[j] != old_ex.path().branches()[j]) {
			return false;
		}
	}
	return (new_ex.path().branches()[branch_idx]
			!= old_ex.path().branches()[branch_idx]);
}
#endif

////////////////////////////////////////////////////////////////////////
//// BoundedDepthFirstSearch ///////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

BoundedDepthFirstSearch::BoundedDepthFirstSearch
	(const string& program, int max_iterations, int max_depth, bool reverse)
	: Search(program, max_iterations), max_depth_(max_depth), reverse_(reverse) { }

BoundedDepthFirstSearch::~BoundedDepthFirstSearch() { }

void BoundedDepthFirstSearch::Run() {
	// Initial execution (on empty/random inputs).
	SymbolicExecution ex = SymbolicExecution();
	RunProgram(vector<Value_t>(), &ex); 
	if(!SYM_assume_violated)
		UpdateCoverage(ex);

	if(reverse_ == true)
		reverse_DFS(0, max_depth_, ex);
	else
		DFS(0,max_depth_,ex);
	// DFS(0, ex);
}

void BoundedDepthFirstSearch::reverse_DFS(size_t pos, int depth, SymbolicExecution& prev_ex) {
	SymbolicExecution cur_ex;
	vector<Value_t> input;

	const SymbolicPath& path = prev_ex.path();

	for (size_t i = pos; (i < path.constraints().size()) && (depth > 0); i++) {
		// Solve constraints[0..i].
		if (!SolveAtBranch(prev_ex, i, &input)) {
			Z3Solver::no_reduction_unsat_formula_length += (i+1);
			Z3Solver::no_reduction_unsat_count++;

			continue;
		}
		Z3Solver::no_reduction_sat_formula_length += (i+1);
		Z3Solver::no_reduction_sat_count++;
	
		SymbolicExecution* ex = new SymbolicExecution();	
		cur_ex = *ex;
		assert(cur_ex.object_tracker()->snapshotManager().size()==0);

		// Run on those constraints.
		cur_ex = SymbolicExecution();
		RunProgram(input, &cur_ex);  

		if(!SYM_assume_violated)
			UpdateCoverage(cur_ex);

		// Check for prediction failure.
		size_t branch_idx = path.constraints_idx()[i];
		if (!CheckPrediction(prev_ex, cur_ex, branch_idx)) {
			fprintf(stderr, "Prediction failed!\n");
			continue;
		}

		// We successfully solved the branch, recurse.
		depth--;

		reverse_DFS(i+1, depth, cur_ex);
	}
}


void BoundedDepthFirstSearch::DFS(size_t pos, int depth, SymbolicExecution& prev_ex) {
	SymbolicExecution cur_ex;
	vector<Value_t> input;

	const SymbolicPath& path = prev_ex.path();

	for (size_t i = path.constraints().size()-1; i < path.constraints().size() && i>=pos && (depth > 0); i--) {
		// Solve constraints[0..i].
		if (!SolveAtBranch(prev_ex, i, &input)) {
			Z3Solver::no_reduction_unsat_formula_length += (i+1);
			Z3Solver::no_reduction_unsat_count++;

			continue;
		}
		Z3Solver::no_reduction_sat_formula_length += (i+1);
		Z3Solver::no_reduction_sat_count++;
	
		SymbolicExecution* ex = new SymbolicExecution();	
		cur_ex = *ex;
		assert(cur_ex.object_tracker()->snapshotManager().size()==0);

		// Run on those constraints.
		cur_ex = SymbolicExecution();
		RunProgram(input, &cur_ex);  

		if(!SYM_assume_violated)
			UpdateCoverage(cur_ex);


		// Check for prediction failure.
		size_t branch_idx = path.constraints_idx()[i];
		if (!CheckPrediction(prev_ex, cur_ex, branch_idx)) {
			fprintf(stderr, "Prediction failed!\n");
			continue;
		}

		// We successfully solved the branch, recurse.
		depth--;

		DFS(i+1, depth, cur_ex);
	}
}


////////////////////////////////////////////////////////////////////////
//// RandomInputSearch /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

RandomInputSearch::RandomInputSearch(const string& program, int max_iterations)
	: Search(program, max_iterations) { }

RandomInputSearch::~RandomInputSearch() { }

void RandomInputSearch::Run() {
	vector<Value_t> input;
	ex_ = SymbolicExecution();
	RunProgram(input, &ex_);

	while (true) {
		RandomInput(ex_.vars(), &input);
		ex_ = SymbolicExecution();
		RunProgram(input, &ex_);

		if(!SYM_assume_violated)
			UpdateCoverage(ex_);
	}
}


////////////////////////////////////////////////////////////////////////
//// RandomSearch //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

RandomSearch::RandomSearch(const string& program, int max_iterations)
	: Search(program, max_iterations) { }

RandomSearch::~RandomSearch() { }

void RandomSearch::Run() {
	SymbolicExecution next_ex = SymbolicExecution();

	while (true) {
		// Execution (on empty/random inputs).
		fprintf(stderr, "RESET\n");
		vector<Value_t> next_input;
		ex_ = SymbolicExecution();
		RunProgram(next_input, &ex_);

		if(!SYM_assume_violated)
			UpdateCoverage(ex_);

		// Do some iterations.
		int count = 0;
		while (count++ < 10000) {
			// fprintf(stderr, "Uncovered bounded DFS.\n");
			// SolveUncoveredBranches(0, 20, ex_);

			size_t idx;
			if (SolveRandomBranch(&next_input, &idx)) {
				next_ex = SymbolicExecution();
				RunProgram(next_input, &next_ex);

				bool found_new_branch= 
					!SYM_assume_violated ? UpdateCoverage(next_ex): false; 
				bool prediction_failed =
					!CheckPrediction(ex_, next_ex, ex_.path().constraints_idx()[idx]);

				if (found_new_branch) {
					count = 0;
					ex_.Swap(next_ex);
					if (prediction_failed)
						fprintf(stderr, "Prediction failed (but got lucky).\n");
				} else if (!prediction_failed) {
					ex_.Swap(next_ex);
				} else {
					fprintf(stderr, "Prediction failed.\n");
				}
			}
		}
	}
}


void RandomSearch::SolveUncoveredBranches(size_t i, int depth,
		SymbolicExecution& prev_ex) {
	if (depth < 0)
		return;

	fprintf(stderr, "position: %zu/%zu (%d)\n",
			i, prev_ex.path().constraints().size(), depth);

	SymbolicExecution cur_ex;
	vector<Value_t> input;

	int cnt = 0;

	for (size_t j = i; j < prev_ex.path().constraints().size(); j++) {
		size_t bid_idx = prev_ex.path().constraints_idx()[j];
		branch_id_t bid = prev_ex.path().branches()[bid_idx];
		if (covered_[paired_branch_[bid]])
			continue;

		if (!SolveAtBranch(prev_ex, j, &input)) {
			if (++cnt == 1000) {
				cnt = 0;
				fprintf(stderr, "Failed to solve at %zu/%zu.\n",
						j, prev_ex.path().constraints().size());
			}
			continue;
		}
		cnt = 0;

		cur_ex = SymbolicExecution();
		RunProgram(input, &cur_ex);
		if(!SYM_assume_violated)
			UpdateCoverage(cur_ex);
		if (!CheckPrediction(prev_ex, cur_ex, bid_idx)) {
			fprintf(stderr, "Prediction failed.\n");
			continue;
		}

		SolveUncoveredBranches(j+1, depth-1, cur_ex);
	}
}


bool RandomSearch::SolveRandomBranch(vector<Value_t>* next_input, size_t* idx) {

	vector<size_t> idxs(ex_.path().constraints().size());
	for (size_t i = 0; i < idxs.size(); i++)
		idxs[i] = i;

	for (int tries = 0; tries < 1000; tries++) {
		// Pick a random index.
		if (idxs.size() == 0)
			break;
		size_t r = rand() % idxs.size();
		size_t i = idxs[r];
		swap(idxs[r], idxs.back());
		idxs.pop_back();

		if (SolveAtBranch(ex_, i, next_input)) {
			fprintf(stderr, "Solved %zu/%zu\n", i, idxs.size());
			*idx = i;
			return true;
		}
	}

	// We failed to solve a branch, so reset the input.
	fprintf(stderr, "FAIL\n");
	next_input->clear();
	return false;
}


////////////////////////////////////////////////////////////////////////
//// RandomSearch //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

UniformRandomSearch::UniformRandomSearch(const string& program,
		int max_iterations,
		size_t max_depth)
	: Search(program, max_iterations), max_depth_(max_depth) { }

	UniformRandomSearch::~UniformRandomSearch() { }

	void UniformRandomSearch::Run() {
		// Initial execution (on empty/random inputs).
		prev_ex_ = SymbolicExecution();
		RunProgram(vector<Value_t>(), &prev_ex_);
		if(!SYM_assume_violated)
			UpdateCoverage(prev_ex_);

		while (true) {
			fprintf(stderr, "RESET\n");

			// Uniform random path.
			DoUniformRandomPath();
		}
	}

void UniformRandomSearch::DoUniformRandomPath() {
	vector<Value_t> input;

	size_t i = 0;
	size_t depth = 0;
	fprintf(stderr, "%zu constraints.\n", prev_ex_.path().constraints().size());
	while ((i < prev_ex_.path().constraints().size()) && (depth < max_depth_)) {
		if (SolveAtBranch(prev_ex_, i, &input)) {
			fprintf(stderr, "Solved constraint %zu/%zu.\n",
					(i+1), prev_ex_.path().constraints().size());
			depth++;

			// With probability 0.5, force the i-th constraint.
			if (rand() % 2 == 0) {
				cur_ex_ = SymbolicExecution();
				RunProgram(input, &cur_ex_);

				if(!SYM_assume_violated)
					UpdateCoverage(cur_ex_);
				size_t branch_idx = prev_ex_.path().constraints_idx()[i];
				if (!CheckPrediction(prev_ex_, cur_ex_, branch_idx)) {
					fprintf(stderr, "prediction failed\n");
					depth--;
				} else {
					cur_ex_.Swap(prev_ex_);
				}
			}
		}

		i++;
	}
}


////////////////////////////////////////////////////////////////////////
//// HybridSearch //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

HybridSearch::HybridSearch(const string& program, int max_iterations, int step_size)
	: Search(program, max_iterations), step_size_(step_size) { }

	HybridSearch::~HybridSearch() { }

	void HybridSearch::Run() {
		SymbolicExecution ex;

		while (true) {
			// Execution on empty/random inputs.
			ex = SymbolicExecution();
			RunProgram(vector<Value_t>(), &ex);
			if(!SYM_assume_violated)
				UpdateCoverage(ex);

			// Local searches at increasingly deeper execution points.
			for (size_t pos = 0; pos < ex.path().constraints().size(); pos += step_size_) {
				RandomLocalSearch(&ex, pos, pos+step_size_);
			}
		}
	}

void HybridSearch::RandomLocalSearch(SymbolicExecution *ex, size_t start, size_t end) {
	for (int iters = 0; iters < 100; iters++) {
		if (!RandomStep(ex, start, end))
			break;
	}
}

bool HybridSearch::RandomStep(SymbolicExecution *ex, size_t start, size_t end) {

	if (end > ex->path().constraints().size()) {
		end = ex->path().constraints().size();
	}
	assert(start < end);

	SymbolicExecution next_ex;
	vector<Value_t> input;

	fprintf(stderr, "%zu-%zu\n", start, end);
	vector<size_t> idxs(end - start);
	for (size_t i = 0; i < idxs.size(); i++) {
		idxs[i] = start + i;
	}

	for (int tries = 0; tries < 1000; tries++) {
		// Pick a random index.
		if (idxs.size() == 0)
			break;
		size_t r = rand() % idxs.size();
		size_t i = idxs[r];
		swap(idxs[r], idxs.back());
		idxs.pop_back();

		if (SolveAtBranch(*ex, i, &input)) {
			next_ex = SymbolicExecution();
			RunProgram(input, &next_ex);
			if(!SYM_assume_violated)
				UpdateCoverage(next_ex);
			if (CheckPrediction(*ex, next_ex, ex->path().constraints_idx()[i])) {
				ex->Swap(next_ex);
				return true;
			}
		}
	}

	return false;
}


////////////////////////////////////////////////////////////////////////
//// CfgBaselineSearch /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

CfgBaselineSearch::CfgBaselineSearch(const string& program, int max_iterations)
	: Search(program, max_iterations) { }

	CfgBaselineSearch::~CfgBaselineSearch() { }


	void CfgBaselineSearch::Run() {
		SymbolicExecution ex = SymbolicExecution();

		while (true) {
			// Execution on empty/random inputs.
			fprintf(stderr, "RESET\n");
			ex = SymbolicExecution();
			RunProgram(vector<Value_t>(), &ex);
			UpdateCoverage(ex);

			while (DoSearch(5, 250, 0, ex)) {
				// As long as we keep finding new branches . . . .
				ex.Swap(success_ex_);
			}
		}
	}


bool CfgBaselineSearch::DoSearch(int depth, int iters, int pos,
		SymbolicExecution& prev_ex) {

	// For each symbolic branch/constraint in the execution path, we will
	// compute a heuristic score, and then attempt to force the branches
	// in order of increasing score.
	vector<ScoredBranch> scoredBranches(prev_ex.path().constraints().size() - pos);
	for (size_t i = 0; i < scoredBranches.size(); i++) {
		scoredBranches[i].first = i + pos;
	}

	{ // Compute (and sort by) the scores.
		random_shuffle(scoredBranches.begin(), scoredBranches.end());
		map<branch_id_t,int> seen;
		for (size_t i = 0; i < scoredBranches.size(); i++) {
			size_t idx = scoredBranches[i].first;
			size_t branch_idx = prev_ex.path().constraints_idx()[idx];
			branch_id_t bid = paired_branch_[prev_ex.path().branches()[branch_idx]];
			if (covered_[bid]) {
				scoredBranches[i].second = 100000000 + seen[bid];
			} else {
				scoredBranches[i].second = seen[bid];
			}
			seen[bid] += 1;
		}
	}
	stable_sort(scoredBranches.begin(), scoredBranches.end(), ScoredBranchComp());

	// Solve.
	SymbolicExecution cur_ex = SymbolicExecution();
	vector<Value_t> input;
	for (size_t i = 0; i < scoredBranches.size(); i++) {
		if (iters <= 0) {
			return false;
		}

		if (!SolveAtBranch(prev_ex, scoredBranches[i].first, &input)) {
			continue;
		}

		cur_ex = SymbolicExecution();
		RunProgram(input, &cur_ex);
		iters--;

		if (UpdateCoverage(cur_ex, NULL)) {
			success_ex_.Swap(cur_ex);
			return true;
		}
	}

	return false;
}


////////////////////////////////////////////////////////////////////////
//// CfgHeuristicSearch ////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

	CfgHeuristicSearch::CfgHeuristicSearch
(const string& program, int max_iterations)
	: Search(program, max_iterations),
	cfg_(max_branch_), cfg_rev_(max_branch_), dist_(max_branch_) {

		// Read in the CFG.
		ifstream in("cfg_branches", ios::in | ios::binary);
		assert(in);
		size_t num_branches;
		in.read((char*)&num_branches, sizeof(num_branches));
		assert(num_branches == branches_.size());
		for (size_t i = 0; i < num_branches; i++) {
			branch_id_t src;
			size_t len;
			in.read((char*)&src, sizeof(src));
			in.read((char*)&len, sizeof(len));
			cfg_[src].resize(len);
			in.read((char*)&cfg_[src].front(), len * sizeof(branch_id_t));
		}
		in.close();

		// Construct the reversed CFG.
		for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
			for (BranchIt j = cfg_[*i].begin(); j != cfg_[*i].end(); ++j) {
				cfg_rev_[*j].push_back(*i);
			}
		}
	}


CfgHeuristicSearch::~CfgHeuristicSearch() { }


void CfgHeuristicSearch::Run() {
	set<branch_id_t> newly_covered_;
	SymbolicExecution ex;

	while (true) {
		covered_.assign(max_branch_, false);
		num_covered_ = 0;

		// Execution on empty/random inputs.
		fprintf(stderr, "RESET\n");
		ex = SymbolicExecution();
		RunProgram(vector<Value_t>(), &ex);

		if (UpdateCoverage(ex)) {
			UpdateBranchDistances();
			//PrintStats();
		}

		// while (DoSearch(3, 200, 0, kInfiniteDistance+10, ex)) {
		while (DoSearch(5, 30, 0, kInfiniteDistance, ex)) {
			// while (DoSearch(3, 10000, 0, kInfiniteDistance, ex)) {
			//PrintStats();
			// As long as we keep finding new branches . . . .
			UpdateBranchDistances();
			ex.Swap(success_ex_);
		}
		//PrintStats();
	}
}


void CfgHeuristicSearch::PrintStats() {
	fprintf(stderr, "Cfg solves: %u/%u (%u lucky [%u continued], %u on 0's, %u on others,"
			"%u unsats, %u prediction failures)\n",
			(num_inner_lucky_successes_ + num_inner_zero_successes_ + num_inner_nonzero_successes_ + num_top_solve_successes_),
			num_inner_solves_, num_inner_lucky_successes_, (num_inner_lucky_successes_ - num_inner_successes_pred_fail_),
			num_inner_zero_successes_, num_inner_nonzero_successes_,
			num_inner_unsats_, num_inner_pred_fails_);
	fprintf(stderr, "    (recursive successes: %u)\n", num_inner_recursive_successes_);
	fprintf(stderr, "Top-level SolveAlongCfg: %u/%u\n",
			num_top_solve_successes_, num_top_solves_);
	fprintf(stderr, "All SolveAlongCfg: %u/%u  (%u all concrete, %u no paths)\n",
			num_solve_successes_, num_solves_,
			num_solve_all_concrete_, num_solve_no_paths_);
	fprintf(stderr, "    (sat failures: %u/%u)  (prediction failures: %u) (recursions: %u)\n",
			num_solve_unsats_, num_solve_sat_attempts_,
			num_solve_pred_fails_, num_solve_recurses_);
}


void CfgHeuristicSearch::UpdateBranchDistances() {
		// We run a BFS backward, starting simultaneously at all uncovered vertices.
		queue<branch_id_t> Q;
		for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
			if (!covered_[*i]) {
				dist_[*i] = 0;
				Q.push(*i);
			} else {
				dist_[*i] = kInfiniteDistance;
			}
		}

		while (!Q.empty()) {
			branch_id_t i = Q.front();
			size_t dist_i = dist_[i];
			Q.pop();

			for (BranchIt j = cfg_rev_[i].begin(); j != cfg_rev_[i].end(); ++j) {
				if (dist_i + 1 < dist_[*j]) {
					dist_[*j] = dist_i + 1;
					Q.push(*j);
				}
			}
		}
	}


bool CfgHeuristicSearch::DoSearch(int depth,
			int iters,
			int pos,
			int maxDist,
			SymbolicExecution& prev_ex) {

	fprintf(stderr, "DoSearch(%d, %d, %d, %zu)\n",
			depth, pos, maxDist, prev_ex.path().branches().size());

	if (pos >= static_cast<int>(prev_ex.path().constraints().size()))
		return false;

	if (depth == 0)
		return false;


	// For each symbolic branch/constraint in the execution path, we will
	// compute a heuristic score, and then attempt to force the branches
	// in order of increasing score.
	vector<ScoredBranch> scoredBranches(prev_ex.path().constraints().size() - pos);
	for (size_t i = 0; i < scoredBranches.size(); i++) {
		scoredBranches[i].first = i + pos;
	}

	{ // Compute (and sort by) the scores.
		random_shuffle(scoredBranches.begin(), scoredBranches.end());
		map<branch_id_t,int> seen;
		for (size_t i = 0; i < scoredBranches.size(); i++) {
			size_t idx = scoredBranches[i].first;
			size_t branch_idx = prev_ex.path().constraints_idx()[idx];
			branch_id_t bid = paired_branch_[prev_ex.path().branches()[branch_idx]];

			scoredBranches[i].second = dist_[bid] + seen[bid];
			seen[bid] += 1;

			/*
			   if (dist_[bid] == 0) {
			   scoredBranches[i].second = 0;
			   } else {
			   scoredBranches[i].second = dist_[bid] + seen[bid];
			   seen[bid] += 1;
			   }
			 */
		}
	}
	stable_sort(scoredBranches.begin(), scoredBranches.end(), ScoredBranchComp());

	// Solve.
	SymbolicExecution cur_ex;
	vector<Value_t> input;
	for (size_t i = 0; i < scoredBranches.size(); i++) {
		if ((iters <= 0) || (scoredBranches[i].second > maxDist))
			return false;

		num_inner_solves_ ++;

		if (!SolveAtBranch(prev_ex, scoredBranches[i].first, &input)) {
			num_inner_unsats_ ++;
			continue;
		}

		cur_ex = SymbolicExecution();
		RunProgram(input, &cur_ex);

		iters--;

		size_t b_idx = prev_ex.path().constraints_idx()[scoredBranches[i].first];
		branch_id_t bid = paired_branch_[prev_ex.path().branches()[b_idx]];
		set<branch_id_t> new_branches;
		bool found_new_branch = UpdateCoverage(cur_ex, &new_branches);
		bool prediction_failed = !CheckPrediction(prev_ex, cur_ex, b_idx);


		if (found_new_branch && prediction_failed) {
			fprintf(stderr, "Prediction failed.\n");
			fprintf(stderr, "Found new branch by forcing at "
					"distance %zu (%d) [lucky, pred failed].\n",
					dist_[bid], scoredBranches[i].second);

			// We got lucky, and can't really compute any further stats
			// because prediction failed.
			num_inner_lucky_successes_ ++;
			num_inner_successes_pred_fail_ ++;
			success_ex_.Swap(cur_ex);
			return true;
		}

		if (found_new_branch && !prediction_failed) {
			fprintf(stderr, "Found new branch by forcing at distance %zu (%d).\n",
					dist_[bid], scoredBranches[i].second);
			size_t min_dist = MinCflDistance(b_idx, cur_ex, new_branches);
			// Check if we were lucky.
			if (FindAlongCfg(b_idx, dist_[bid], cur_ex, new_branches)) {
				assert(min_dist <= dist_[bid]);
				// A legitimate find -- return success.
				if (dist_[bid] == 0) {
					num_inner_zero_successes_ ++;
				} else {
					num_inner_nonzero_successes_ ++;
				}
				success_ex_.Swap(cur_ex);
				return true;
			} else {
				// We got lucky, but as long as there were no prediction failures,
				// we'll finish the CFG search to see if that works, too.
				assert(min_dist > dist_[bid]);
				assert(dist_[bid] != 0);
				num_inner_lucky_successes_ ++;
			}
		}

		if (prediction_failed) {
			fprintf(stderr, "Prediction failed.\n");
			if (!found_new_branch) {
				num_inner_pred_fails_ ++;
				continue;
			}
		}

		// If we reached here, then scoredBranches[i].second is greater than 0.
		num_top_solves_ ++;
		if ((dist_[bid] > 0) &&
				SolveAlongCfg(b_idx, scoredBranches[i].second-1, cur_ex)) {
			num_top_solve_successes_ ++;
			PrintStats();
			return true;
		}

		if (found_new_branch) {
			success_ex_.Swap(cur_ex);
			return true;
		}

		/*
		   if (DoSearch(depth-1, 5, scoredBranches[i].first+1, scoredBranches[i].second-1, cur_ex)) {
		   num_inner_recursive_successes_ ++;
		   return true;
		   }
		 */
	}

	return false;
}


size_t CfgHeuristicSearch::MinCflDistance
	(size_t i, const SymbolicExecution& ex, const set<branch_id_t>& bs) {

	const vector<branch_id_t>& p = ex.path().branches();

	if (i >= p.size())
		return numeric_limits<size_t>::max();

	if (bs.find(p[i]) != bs.end())
		return 0;

	vector<size_t> stack;
	size_t min_dist = numeric_limits<size_t>::max();
	size_t cur_dist = 1;

	fprintf(stderr, "Found uncovered branches at distances:");
	for (BranchIt j = p.begin()+i+1; j != p.end(); ++j) {
		if (bs.find(*j) != bs.end()) {
			min_dist = min(min_dist, cur_dist);
			fprintf(stderr, " %zu", cur_dist);
		}

		if (*j >= 0) {
			cur_dist++;
		} else if (*j == kCallId) {
			stack.push_back(cur_dist);
		} else if (*j == kReturnId) {
			if (stack.size() == 0)
				break;
			cur_dist = stack.back();
			stack.pop_back();
		} else {
			fprintf(stderr, "\nBad branch id: %d\n", *j);
			exit(1);
		}
	}

	fprintf(stderr, "\n");
	return min_dist;
}

bool CfgHeuristicSearch::FindAlongCfg(size_t i, unsigned int dist,
		const SymbolicExecution& ex,
		const set<branch_id_t>& bs) {

	const vector<branch_id_t>& path = ex.path().branches();

	if (i >= path.size())
		return false;

	branch_id_t bid = path[i];
	if (bs.find(bid) != bs.end())
		return true;

	if (dist == 0)
		return false;

	// Compute the indices of all branches on the path that immediately
	// follow the current branch (corresponding to the i-th constraint)
	// in the CFG. For example, consider the path:
	//     * ( ( ( 1 2 ) 4 ) ( 5 ( 6 7 ) ) 8 ) 9
	// where '*' is the current branch.  The branches immediately
	// following '*' are : 1, 4, 5, 8, and 9.
	vector<size_t> idxs;
	{ size_t pos = i + 1;
		CollectNextBranches(path, &pos, &idxs);
	}

	for (vector<size_t>::const_iterator j = idxs.begin(); j != idxs.end(); ++j) {
		if (FindAlongCfg(*j, dist-1, ex, bs))
			return true;
	}

	return false;
}


bool CfgHeuristicSearch::SolveAlongCfg(size_t i, unsigned int max_dist,
			SymbolicExecution& prev_ex) {
	num_solves_ ++;

	fprintf(stderr, "SolveAlongCfg(%zu,%u)\n", i, max_dist);
	SymbolicExecution cur_ex;
	vector<Value_t> input;
	const vector<branch_id_t>& path = prev_ex.path().branches();

	// Compute the indices of all branches on the path that immediately
	// follow the current branch (corresponding to the i-th constraint)
	// in the CFG. For example, consider the path:
	//     * ( ( ( 1 2 ) 4 ) ( 5 ( 6 7 ) ) 8 ) 9
	// where '*' is the current branch.  The branches immediately
	// following '*' are : 1, 4, 5, 8, and 9.
	bool found_path = false;
	vector<size_t> idxs;
	{ size_t pos = i + 1;
		CollectNextBranches(path, &pos, &idxs);
		// fprintf(stderr, "Branches following %d:", path[i]);
		for (size_t j = 0; j < idxs.size(); j++) {
			// fprintf(stderr, " %d(%u,%u,%u)", path[idxs[j]], idxs[j],
			//      dist_[path[idxs[j]]], dist_[paired_branch_[path[idxs[j]]]]);
			if ((dist_[path[idxs[j]]] <= max_dist)
					|| (dist_[paired_branch_[path[idxs[j]]]] <= max_dist))
				found_path = true;
		}
		//fprintf(stderr, "\n");
	}

	if (!found_path) {
		num_solve_no_paths_ ++;
		return false;
	}

	bool all_concrete = true;
	num_solve_all_concrete_ ++;

	// We will iterate through these indices in some order (random?
	// increasing order of distance? decreasing?), and try to force and
	// recurse along each one with distance no greater than max_dist.
	random_shuffle(idxs.begin(), idxs.end());
	for (vector<size_t>::const_iterator j = idxs.begin(); j != idxs.end(); ++j) {
		// Skip if distance is wrong.
		if ((dist_[path[*j]] > max_dist)
				&& (dist_[paired_branch_[path[*j]]] > max_dist)) {
			continue;
		}

		if (dist_[path[*j]] <= max_dist) {
			// No need to force, this branch is on a shortest path.
			num_solve_recurses_ ++;
			if (SolveAlongCfg(*j, max_dist-1, prev_ex)) {
				num_solve_successes_ ++;
				return true;
			}
		}

		// Find the constraint corresponding to branch idxs[*j].
		vector<size_t>::const_iterator idx =
			lower_bound(prev_ex.path().constraints_idx().begin(),
					prev_ex.path().constraints_idx().end(), *j);
		if ((idx == prev_ex.path().constraints_idx().end()) || (*idx != *j)) {
			continue;  // Branch is concrete.
		}
		size_t c_idx = idx - prev_ex.path().constraints_idx().begin();

		if (all_concrete) {
			all_concrete = false;
			num_solve_all_concrete_ --;
		}

		if(dist_[paired_branch_[path[*j]]] <= max_dist) {
			num_solve_sat_attempts_ ++;
			// The paired branch is along a shortest path, so force.
			if (!SolveAtBranch(prev_ex, c_idx, &input)) {
				num_solve_unsats_ ++;
				continue;
			}
			cur_ex = SymbolicExecution();
			RunProgram(input, &cur_ex);
			if (UpdateCoverage(cur_ex)) {
				num_solve_successes_ ++;
				success_ex_.Swap(cur_ex);
				return true;
			}
			if (!CheckPrediction(prev_ex, cur_ex, *j)) {
				num_solve_pred_fails_ ++;
				continue;
			}

			// Recurse.
			num_solve_recurses_ ++;
			if (SolveAlongCfg(*j, max_dist-1, cur_ex)) {
				num_solve_successes_ ++;
				return true;
			}
		}
	}

	return false;
}

void CfgHeuristicSearch::SkipUntilReturn(const vector<branch_id_t> path, size_t* pos) {
	while ((*pos < path.size()) && (path[*pos] != kReturnId)) {
		if (path[*pos] == kCallId) {
			(*pos)++;
			SkipUntilReturn(path, pos);
			if (*pos >= path.size())
				return;
			assert(path[*pos] == kReturnId);
		}
		(*pos)++;
	}
}

void CfgHeuristicSearch::CollectNextBranches
(const vector<branch_id_t>& path, size_t* pos, vector<size_t>* idxs) {
	// fprintf(stderr, "Collect(%u,%u,%u)\n", path.size(), *pos, idxs->size());

	// Eat an arbitrary sequence of call-returns, collecting inside each one.
	while ((*pos < path.size()) && (path[*pos] == kCallId)) {
		(*pos)++;
		CollectNextBranches(path, pos, idxs);
		SkipUntilReturn(path, pos);
		if (*pos >= path.size())
			return;
		assert(path[*pos] == kReturnId);
		(*pos)++;
	}

	// If the sequence of calls is followed by a branch, add it.
	if ((*pos < path.size()) && (path[*pos] >= 0)) {
		idxs->push_back(*pos);
		(*pos)++;
		return;
	}

	// Alternatively, if the sequence is followed by a return, collect the branches
	// immediately following the return.
	/*
	   if ((*pos < path.size()) && (path[*pos] == kReturnId)) {
	   (*pos)++;
	   CollectNextBranches(path, pos, idxs);
	   }
	 */
}


bool CfgHeuristicSearch::DoBoundedBFS(int i, int depth, SymbolicExecution& prev_ex) {
	if (depth <= 0)
		return false;

	fprintf(stderr, "%d (%d: %d) (%d: %d)\n", depth,
			i-1, prev_ex.path().branches()[prev_ex.path().constraints_idx()[i-1]],
			i, prev_ex.path().branches()[prev_ex.path().constraints_idx()[i]]);

	SymbolicExecution cur_ex;
	vector<Value_t> input;
	const vector<SymbolicExpr*>& constraints = prev_ex.path().constraints();
	for (size_t j = static_cast<size_t>(i); j < constraints.size(); j++) {
		if (!SolveAtBranch(prev_ex, j, &input)) {
			continue;
		}
		cur_ex = SymbolicExecution();
		RunProgram(input, &cur_ex);

		iters_left_--;
		if (UpdateCoverage(cur_ex)) {
			success_ex_.Swap(cur_ex);
			return true;
		}

		if (!CheckPrediction(prev_ex, cur_ex, prev_ex.path().constraints_idx()[j])) {
			fprintf(stderr, "Prediction failed!\n");
			continue;
		}
		int result1 = DoBoundedBFS(j+1, depth-1, cur_ex);
		int result2 = DoBoundedBFS(j+1, depth-1, prev_ex);
		return result1 || result2;
	}

	return false;
}

}  // namespace crown
