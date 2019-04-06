/* CROWN_replay library source code */

#include <stdio.h>
#include <string.h>
#include "../libcrown/crown.h"
#include "../base/basic_functions.h"

#define SIZE 255
#define FILE_NOT_EXIST "crown_replay: Input file '%s' does not exist\n"
#define NO_AVAILABLE_SYM_VAL "crown_replay: No available symbolic value in the input file\n"
#define NON_NUMBER_SYM_VAL "crown_replay: Non-number symbolic value: %s"
#define NON_BINARY_SYM_VAL "crown_replay: Non-binary symbolic value: %s"
#define OVERFLOW_OCCURS "crown_replay: Symbolic value %lli is too big or small for '%s'\n"
#define OVERFLOW_OCCURS_UNSIGNED "crown_replay: Symbolic value %llu is too big for '%s'\n"
#define OVERFLOW_OCCURS_STRING "crown_replay: Symbolic value %s is too big or small for '%s'\n"


static FILE *f = NULL;
static char *tc_file = NULL;

// Converts binary string (of length 32) to float.
float binStringToFloat(const char* binFloat){
    unsigned long long intNum = 0;
    for(int i = 0; i < 32 ;i++){
        intNum <<= 1;
        intNum += binFloat[i] - '0';
    }

    float result;
    memcpy(&result,&intNum,sizeof(result));
    return result;
}

// Converts binary string (of length 64) to double.
double binStringToDouble(const char* binDouble){
    unsigned long long intNum = 0;
    for(int i = 0; i < 64 ;i++){
        intNum <<= 1;
        intNum += binDouble[i] - '0';
    }

    double result;
    memcpy(&result,&intNum,sizeof(result));
    return result;
}

// Check if the buffer content is a number.
bool isnumber(char *buf)
{
    int len = strlen(buf);
    // If the buffer length is 0, return false.
    if(len == 0) return false;

    for(int i=0; i<len; i++)
        // If a character is '\n', break;
        // It means that it is the end of buffer.
        if(buf[i] == '\n')
            break;
        // If a character is not a digit, return false.
        else if(!isdigit(buf[i]))
            return false;
    return true;
}

// Check if the buffer content is a binary.
bool isbinary(char *buf)
{
    int len = strlen(buf);
    // If the buffer length is 0, return false.
    if(len == 0) return false;

    for(int i=0; i<len; i++)
        // If a character is '\n', break;
        // It means that it is the end of buffer.
        if(buf[i] == '\n')
            break;
        // If a character is neither '0' nor '1', return false.
        else if(buf[i] != '0' && buf[i] != '1')
            return false;
    return true;
}

// When CROWN function is called for the first time,
// (i.e., f is not initialized yet)
// raed the input file.
void read_input_file()
{
    if(!f)
    {
        // Read the file name of test_input from the environment CROWN_TC_FILE.
        // (CROWN_replay sets this value)
        tc_file = getenv("CROWN_TC_FILE");
        if (tc_file == NULL)
            tc_file="input";
        f=fopen(tc_file,"r");
        // If the input file does not exist, exit program.
        if(!f)
        {
            fprintf(stderr, FILE_NOT_EXIST, tc_file);
            exit(1);
        }
    }
}

// Returns true if overflow occurs when the symbolic value is assigned to
// certain type of symbolic variable.
// (for signed variable)
bool overflow_occurs(long long value, int size)
{
    long long max = (1ULL<<(8*size-1))-1;
    long long min = ~max;
    return (value > max) || (value < min);
}

// Returns true if overflow occurs when the symbolic value is assigned to
// certain type of symbolic variable.
// (For unsigned variable)
bool overflow_occurs_unsigned(unsigned long long value, int size)
{
    unsigned long long max ;   
    if(size < 8)
        max= (1ULL<<(8*size))-1;
    else
        max = -1;
    unsigned long long min = 0;
    return (value > max) || (value < min);
}

// Returns true if overflow occurs when the symbolic value is assigned to
// certain type of symbolic variable.
// (for both signed and unsigned variable)
bool overflow_occurs_string(const char *buf, int size)
{
    unsigned long long value = strtoull(buf, NULL, 10);
    unsigned long long max;
    if(size < 8)
        max= (1ULL<<(8*size))-1;
    else
        max = -1; 
    unsigned long long min = 0;
    return (value > max) || (value < min);
}

unsigned char __CrownUChar(int cnt_sym_var, int ln, char* fname, ...)
{
    read_input_file();

    char buf[SIZE];
    unsigned char x;
    // Read the type, but it will not be used.
    fgets(buf,sizeof(buf), f);

    // Read the value, and if the value does not exist, exit program.
    if(!fgets(buf,sizeof(buf),f))
    {
        fprintf(stderr,NO_AVAILABLE_SYM_VAL);
        abort();;
    }
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        abort();;
    }
    else
    {
        unsigned long long ull = strtoull(buf,NULL,10);
        // Check if overflow occurs, and exit program if so.
        if(overflow_occurs_unsigned(ull,sizeof(unsigned char)))
        {
            fprintf(stderr,OVERFLOW_OCCURS_UNSIGNED, ull, "unsigned char");
            abort();;
        }
        else
            x =(unsigned char)ull;
    }
    return x;
}

unsigned short __CrownUShort(int cnt_sym_var, int ln, char* fname, ...)
{
    read_input_file();

    char buf[SIZE];
    unsigned short x;
    // Read the type, but it will not be used.
    fgets(buf,sizeof(buf), f);

    // Read the value, and if the value does not exist, exit program.
    if(!fgets(buf,sizeof(buf),f))
    {
        fprintf(stderr,NO_AVAILABLE_SYM_VAL);
        abort();;
    }
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        abort();;
    }
    else
    {
        unsigned long long ull = strtoull(buf,NULL,10);
        // Check if overflow occurs, and exit program if so.
        if(overflow_occurs_unsigned(ull,sizeof(unsigned short)))
        {
            fprintf(stderr,OVERFLOW_OCCURS_UNSIGNED, ull, "unsigned short");
            abort();;
        }
        else
            x =(unsigned short)ull;
    }
    return x;
}

unsigned int __CrownUInt(int cnt_sym_var, int ln, char* fname, ...)
{
    read_input_file();

    char buf[SIZE];
    unsigned int x;
    // Read the type, but it will not be used.
    fgets(buf,sizeof(buf), f);

    // Read the value, and if the value does not exist, exit program.
    if(!fgets(buf,sizeof(buf),f))
    {
        fprintf(stderr,NO_AVAILABLE_SYM_VAL);
        abort();;
    }
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        abort();;
    }
    else
    {
        unsigned long long ull = strtoull(buf,NULL,10);
        // Check if overflow occurs, and exit program if so.
        if(overflow_occurs_unsigned(ull,sizeof(unsigned int)))
        {
            fprintf(stderr, OVERFLOW_OCCURS_UNSIGNED, ull, "unsigned int");
            abort();;
        }
        else
            x =(unsigned int)ull;
   }
   return x;
}

unsigned long __CrownULong(int cnt_sym_var, int ln, char* fname, ...)
{
    read_input_file();

    char buf[SIZE];
    unsigned long x;
    // Read the type, but it will not be used.
    fgets(buf,sizeof(buf), f);

    // Read the value, and if the value does not exist, exit program.
    if(!fgets(buf,sizeof(buf),f))
    {
        fprintf(stderr,NO_AVAILABLE_SYM_VAL);
        abort();;
    }
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        abort();;
    }
    else
    {
        unsigned long long ull = strtoull(buf,NULL,10);
        // Check if overflow occurs, and exit program if so.
        if(overflow_occurs_unsigned(ull,sizeof(unsigned long)))
        {
            fprintf(stderr, OVERFLOW_OCCURS_UNSIGNED, ull, "unsigned long");
            abort();;
        }
        else
            x =(unsigned long)ull;
    }
    return x;
}

unsigned long long __CrownULongLong(int cnt_sym_var, int ln, char* fname, ...)
{
    read_input_file();

    char buf[SIZE];
    unsigned long long x;
    // Read the type, but it will not be used.
    fgets(buf,sizeof(buf), f);

    // Read the value, and if the value does not exist, exit program.
    if(!fgets(buf,sizeof(buf),f))
    {
        fprintf(stderr,NO_AVAILABLE_SYM_VAL);
        abort();;
    }
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        abort();;
    }
    else
    {
        unsigned long long ull = strtoull(buf,NULL,10);
        // Check if overflow occurs, and exit program if so.
        if(overflow_occurs_unsigned(ull,sizeof(unsigned long long)))
        {
            fprintf(stderr,OVERFLOW_OCCURS_UNSIGNED, ull, "unsigned long long");
            abort();;
        }
        else
            x =(unsigned long long)ull;
    }
    return x;
}

char __CrownChar(int cnt_sym_var, int ln, char* fname, ...)
{
    read_input_file();

    char buf[SIZE];
    char x;
    // Read the type, but it will not be used.
    fgets(buf,sizeof(buf), f);

    // Read the value, and if the value does not exist, exit program.
    if(!fgets(buf,sizeof(buf),f))
    {
        fprintf(stderr,NO_AVAILABLE_SYM_VAL);
        abort();;
    }
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        abort();;
    }
    // Check if overflow occurs, and exit program if so.
    else if(overflow_occurs_string(buf,sizeof(char)))
    {
        fprintf(stderr, OVERFLOW_OCCURS_STRING, buf, "char");
        abort();;
    }
    else
    {
        long long ll = strtoll(buf,NULL,10);
        x =(char)ll;
    }
    return x;
}

short __CrownShort(int cnt_sym_var, int ln, char* fname, ...)
{
    read_input_file();

    char buf[SIZE];
    short x;
    // Read the type, but it will not be used.
    fgets(buf,sizeof(buf), f);

    // Read the value, and if the value does not exist, exit program.
    if(!fgets(buf,sizeof(buf),f))
    {
        fprintf(stderr,NO_AVAILABLE_SYM_VAL);
        abort();;
    }
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        abort();;
    }
    // Check if overflow occurs, and exit program if so.
    else if(overflow_occurs_string(buf,sizeof(short)))
    {
        fprintf(stderr, OVERFLOW_OCCURS_STRING, buf, "short");
        abort();;
    }
    else
    {
        long long ll = strtoll(buf,NULL,10);
        x =(short)ll;
    }
    return x;
}

int __CrownInt(int cnt_sym_var, int ln, char* fname, ...)
{
    read_input_file();

    char buf[SIZE];
    int x;
    // Read the type, but it will not be used.
    fgets(buf,sizeof(buf), f);

    // Read the value, and if the value does not exist, exit program.
    if(!fgets(buf,sizeof(buf),f))
    {
        fprintf(stderr,NO_AVAILABLE_SYM_VAL);
        abort();;
    }
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        abort();;
    }
    // Check if overflow occurs, and exit program if so.
    else if(overflow_occurs_string(buf,sizeof(int)))
    {
        fprintf(stderr, OVERFLOW_OCCURS_STRING, buf, "int");
        abort();;
    }
    else
    {
        long long ll = strtoll(buf,NULL,10);
        x =(int)ll;
    }
    return x;
}

long __CrownLong(int cnt_sym_var, int ln, char* fname, ...)
{
    read_input_file();

    char buf[SIZE];
    long x;
    // Read the type, but it will not be used.
    fgets(buf,sizeof(buf), f);

    // Read the value, and if the value does not exist, exit program.
    if(!fgets(buf,sizeof(buf),f))
    {
        fprintf(stderr,NO_AVAILABLE_SYM_VAL);
        abort();;
    }
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        abort();;
    }
    // Check if overflow occurs, and exit program if so.
    else if(overflow_occurs_string(buf,sizeof(long)))
    {
        fprintf(stderr, OVERFLOW_OCCURS_STRING, buf, "long");
        abort();;
    }
    else
    {
        long long ll = strtoll(buf,NULL,10);
        x =(long)ll;
    }
    return x;
}

long long __CrownLongLong(int cnt_sym_var, int ln, char* fname, ...)
{
    read_input_file();

    char buf[SIZE];
    long long x;
    // Read the type, but it will not be used.
    fgets(buf,sizeof(buf), f);

    // Read the value, and if the value does not exist, exit program.
    if(!fgets(buf,sizeof(buf),f))
    {
        fprintf(stderr,NO_AVAILABLE_SYM_VAL);
        abort();;
    }
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        abort();;
    }
    // Check if overflow occurs, and exit program if so.
    else if(overflow_occurs_string(buf,sizeof(long long)))
    {
        fprintf(stderr, OVERFLOW_OCCURS_STRING, buf, "long long");
        abort();;
    }
    else
    {
        long long ll = strtoll(buf,NULL,10);
        x =(long long)ll;
    }
    return x;
}

float __CrownFloat(int cnt_sym_var, int ln, char* fname, ...)
{
    read_input_file();

    char buf[SIZE];
    float x;
    // Read the type, but it will not be used.
    fgets(buf,sizeof(buf), f);

    // Read the value, and if the value does not exist, exit program.
    if(!fgets(buf,sizeof(buf),f))
    {
        fprintf(stderr,NO_AVAILABLE_SYM_VAL);
        abort();;
    }
    // If the value is not a binary, exit program.
    else if(!isbinary(buf))
    {
        fprintf(stderr,NON_BINARY_SYM_VAL,buf);
        abort();;
    }
    else {
        // Symbolic value for float is a binary string format.
        x = binStringToFloat(buf);
    }
    return x;
}

double __CrownDouble(int cnt_sym_var, int ln, char* fname, ...)
{
    read_input_file();

    char buf[SIZE];
    double x;
    // Read the type, but it will not be used.
    fgets(buf,sizeof(buf), f);

    // Read the value, and if the value does not exist, exit program.
    if(!fgets(buf,sizeof(buf),f))
    {
        fprintf(stderr,NO_AVAILABLE_SYM_VAL);
        abort();;
    }
    // If the value is not a binary, exit program.
    else if(!isbinary(buf))
    {
        fprintf(stderr,NON_BINARY_SYM_VAL,buf);
        abort();;
    }
    else{
        // Symbolic value for double is a binary string format.
        x = binStringToDouble(buf);
    }
    return x;
}

// Kunwoo Park (2018-11-09) : Renaming __CrownUChar2() -> __CrownUCharInit() and etc.
unsigned char __CrownUCharInit(unsigned char* x, unsigned char val, int cnt_sym_var, int ln, char* fname, ...){
    return __CrownUChar(cnt_sym_var, ln, fname);
}

unsigned short __CrownUShortInit(unsigned short* x, unsigned short val, int cnt_sym_var, int ln, char* fname, ...){
    return __CrownUShort(cnt_sym_var, ln, fname);
}

unsigned int __CrownUIntInit(unsigned int* x, unsigned int val, int cnt_sym_var, int ln, char* fname, ...){
    return __CrownUInt(cnt_sym_var, ln, fname);
}

unsigned long __CrownULongInit(unsigned long* x, unsigned long val, int cnt_sym_var, int ln, char* fname, ...){
    return __CrownULong(cnt_sym_var, ln, fname);
}

unsigned long long __CrownULongLongInit(unsigned long long* x, unsigned long long val, int cnt_sym_var, int ln, char* fname, ...){
    return __CrownULongLong(cnt_sym_var, ln, fname);
}

char  __CrownCharInit(char* x, char val, int cnt_sym_var, int ln, char* fname, ...){
    return __CrownChar(cnt_sym_var, ln, fname);
}

short __CrownShortInit(short* x, short val, int cnt_sym_var, int ln, char* fname, ...){
    return __CrownShort(cnt_sym_var, ln, fname);
}

int __CrownIntInit(int* x, int val, int cnt_sym_var, int ln, char* fname, ...){
    return __CrownInt(cnt_sym_var, ln, fname);
}

long __CrownLongInit(long * x, long val, int cnt_sym_var, int ln, char* fname, ...){
    return __CrownLong(cnt_sym_var, ln, fname);
}

long long __CrownLongLongInit(long long * x, long long val, int cnt_sym_var, int ln, char* fname, ...){
    return __CrownLongLong(cnt_sym_var, ln, fname);
}

float __CrownFloatInit(float * x, float val, int cnt_sym_var, int ln, char* fname, ...){
    return __CrownFloat(cnt_sym_var, ln, fname);
}

double __CrownDoubleInit(double * x, double val, int cnt_sym_var, int ln, char* fname, ...){
    return __CrownDouble(cnt_sym_var, ln, fname);
}

void __CrownLongDoubleInit(long double * x, long double val, int cnt_sym_var, int ln, char* fname, ...){
   puts("crown_replay: SYM_longdouble_init() is not supported yet ");
   exit (-1);
}

void __CrownLongDouble(long double *x, int cnt_sym_var, int ln, char* fname, ...)
{
    puts("crown_replay: SYM_longdouble() is not supported yet ");
    exit(-1);
#if 0
    read_input_file();

    char buf[SIZE];
    // Read the type, but it will not be used.
    fgets(buf,sizeof(buf), f);

    // Read the value, and if the value does not exist, exit program.
    if(!fgets(buf,sizeof(buf),f))
    {
        fprintf(stderr,NO_AVAILABLE_SYM_VAL);
        exit(1);
    }
    // If the value is not a binary, exit program.
    else if(!isbinary(buf))
    {
        fprintf(stderr,NON_BINARY_SYM_VAL,buf);
        exit(1);
    }
    else
        *x = strtold(buf,NULL);
#endif
}

unsigned long long __CrownBitField(unsigned char * x, char unionSize, int lowestBit, int highestBit, int cnt_sym_var, int ln, char * fname, ...){
		
		read_input_file();

    char buf[SIZE];
    // Read the type,
    fgets(buf,sizeof(buf), f);
		int hBit = 0,lBit = 0,indexSize = 0,bfsize = 0;
		unsigned long long result= 0, ll= 0;
		int i = 0;

		char * bufblock;

		bufblock = strtok(buf, " ");
		bufblock = strtok(NULL, " ");
		hBit = atoi(bufblock);
		bufblock = strtok(NULL, " ");
		lBit = atoi (bufblock);
		bufblock = strtok(NULL, " ");
		indexSize = atoi(bufblock);
		bfsize = 0;

		if(indexSize == 0){ //union

				if(!fgets(buf,sizeof(buf),f))
				{
						fprintf(stderr,NO_AVAILABLE_SYM_VAL);
						exit(1);
				}
				// If the value is not a number, exit program.
				else if(!isnumber(buf))
				{
						fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
						exit(1);
				}
				// Check if overflow occurs, and exit program if so.
				else if(overflow_occurs_string(buf,sizeof(char)))
				{
						fprintf(stderr, OVERFLOW_OCCURS_STRING, buf, "char");
					 exit(1);
				}
				else
				{
					 ll = strtoll(buf,NULL,10);	
					 result = (ll >> lBit) & ((1ULL << (hBit - lBit)) - 1);
					 return result;
			 }
		} else { //struct
				for ( i = 0; i < indexSize; i++){
					// Read the value, and if the value does not exist, exit program.
					if(!fgets(buf,sizeof(buf),f))
					{
							fprintf(stderr,NO_AVAILABLE_SYM_VAL);
							exit(1);
					}
					// If the value is not a number, exit program.
					else if(!isnumber(buf))
					{
							fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
							exit(1);
					}
					// Check if overflow occurs, and exit program if so.
					else if(overflow_occurs_string(buf,sizeof(char)))
					{
							fprintf(stderr, OVERFLOW_OCCURS_STRING, buf, "char");
						 exit(1);
				 }
				 else
				 {
						 ll = strtoll(buf,NULL,10);	
						 result = (((ll >> lBit) & ( (1ULL << (hBit - lBit)) - 1)) << bfsize) | result;
						 bfsize += (hBit - lBit);

						 if( i == indexSize - 1) return result;
				 }

				 read_input_file();
				 fgets(buf,sizeof(buf), f);

				 bufblock = strtok(buf, " ");
				 bufblock = strtok(NULL, " ");
				 hBit = atoi(bufblock);
				 bufblock = strtok(NULL, " ");
				 lBit = atoi(bufblock);
				}
		}

		return 0; //should not be reached.

}
