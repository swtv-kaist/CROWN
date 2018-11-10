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

void __CrownUChar(unsigned char *x, int cnt_sym_var, int ln, char* fname, ...)
{
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
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        exit(1);
    }
    else
    {
        unsigned long long ull = strtoull(buf,NULL,10); 
        // Check if overflow occurs, and exit program if so.
        if(overflow_occurs_unsigned(ull,sizeof(unsigned char)))
        {
            fprintf(stderr,OVERFLOW_OCCURS_UNSIGNED, ull, "unsigned char");
            exit(1);
        }
        else
            *x =(unsigned char)ull;
    }
}
void __CrownUShort(unsigned short *x, int cnt_sym_var, int ln, char* fname, ...)
{
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
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        exit(1);
    }
    else
    {
        unsigned long long ull = strtoull(buf,NULL,10);
        // Check if overflow occurs, and exit program if so.
        if(overflow_occurs_unsigned(ull,sizeof(unsigned short)))
        {
            fprintf(stderr,OVERFLOW_OCCURS_UNSIGNED, ull, "unsigned short");
            exit(1);
        }
        else
            *x =(unsigned short)ull;
    }
}
void __CrownUInt(unsigned int *x, int cnt_sym_var, int ln, char* fname, ...)
{
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
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        exit(1);
    }
    else
    {
        unsigned long long ull = strtoull(buf,NULL,10);
        // Check if overflow occurs, and exit program if so.
        if(overflow_occurs_unsigned(ull,sizeof(unsigned int)))
        {
            fprintf(stderr, OVERFLOW_OCCURS_UNSIGNED, ull, "unsigned int");
            exit(1);
        }
        else
            *x =(unsigned int)ull;
   }
}
void __CrownULong(unsigned long *x, int cnt_sym_var, int ln, char* fname, ...)
{
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
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        exit(1);
    }
    else
    {
        unsigned long long ull = strtoull(buf,NULL,10);
        // Check if overflow occurs, and exit program if so.
        if(overflow_occurs_unsigned(ull,sizeof(unsigned long)))
        {
            fprintf(stderr, OVERFLOW_OCCURS_UNSIGNED, ull, "unsigned long");
            exit(1);
        }
        else
            *x =(unsigned long)ull;
    }
}
void __CrownULongLong(unsigned long long *x, int cnt_sym_var, int ln, char* fname, ...)
{
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
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        exit(1);
    }
    else
    {
        unsigned long long ull = strtoull(buf,NULL,10);
        // Check if overflow occurs, and exit program if so.
        if(overflow_occurs_unsigned(ull,sizeof(unsigned long long)))
        {
            fprintf(stderr,OVERFLOW_OCCURS_UNSIGNED, ull, "unsigned long long");
            exit(1);
        }
        else
            *x =(unsigned long long)ull;
    }
}
void __CrownChar(char *x, int cnt_sym_var, int ln, char* fname, ...)
{
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
        long long ll = strtoll(buf,NULL,10);
        *x =(char)ll;
    }
}
void __CrownShort(short *x, int cnt_sym_var, int ln, char* fname, ...)
{
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
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        exit(1);
    }
    // Check if overflow occurs, and exit program if so.
    else if(overflow_occurs_string(buf,sizeof(short)))
    {
        fprintf(stderr, OVERFLOW_OCCURS_STRING, buf, "short");
        exit(1);
    }
    else
    {
        long long ll = strtoll(buf,NULL,10);
        *x =(short)ll;
    }
}
void __CrownInt(int *x, int cnt_sym_var, int ln, char* fname, ...)
{
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
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        exit(1);
    }
    // Check if overflow occurs, and exit program if so.
    else if(overflow_occurs_string(buf,sizeof(int)))
    {
        fprintf(stderr, OVERFLOW_OCCURS_STRING, buf, "int");
        exit(1);
    }
    else
    {
        long long ll = strtoll(buf,NULL,10);
        *x =(int)ll;
    }
}
void __CrownLong(long *x, int cnt_sym_var, int ln, char* fname, ...)
{
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
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        exit(1);
    }
    // Check if overflow occurs, and exit program if so.
    else if(overflow_occurs_string(buf,sizeof(long)))
    {
        fprintf(stderr, OVERFLOW_OCCURS_STRING, buf, "long");
        exit(1);
    }
    else
    {
        long long ll = strtoll(buf,NULL,10);
        *x =(long)ll;
    }
}
void __CrownLongLong(long long *x, int cnt_sym_var, int ln, char* fname, ...)
{
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
    // If the value is not a number, exit program.
    else if(!isnumber(buf))
    {
        fprintf(stderr,NON_NUMBER_SYM_VAL,buf);
        exit(1);
    }
    // Check if overflow occurs, and exit program if so.
    else if(overflow_occurs_string(buf,sizeof(long long)))
    {
        fprintf(stderr, OVERFLOW_OCCURS_STRING, buf, "long long");
        exit(1);
    }
    else
    {
        long long ll = strtoll(buf,NULL,10);
        *x =(long long)ll;
    }
}
void __CrownFloat(float *x, int cnt_sym_var, int ln, char* fname, ...)
{
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
    else {
        // Symbolic value for float is a binary string format.
        *x = binStringToFloat(buf);
    }
}
void __CrownDouble(double *x, int cnt_sym_var, int ln, char* fname, ...)
{
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
        // Symbolic value for double is a binary string format.
        *x = binStringToDouble(buf);
}
// Kunwoo Park (2018-11-09) : Renaming __CrownUChar2() -> __CrownUCharInit() and etc.
void __CrownUCharInit(unsigned char* x, unsigned char val, int cnt_sym_var, int ln, char* fname, ...){
    __CrownUChar(x, cnt_sym_var, ln, fname);
}

void __CrownUShortInit(unsigned short* x, unsigned short val, int cnt_sym_var, int ln, char* fname, ...){
    __CrownUShort(x, cnt_sym_var, ln, fname);
}

void __CrownUIntInit(unsigned int* x, unsigned int val, int cnt_sym_var, int ln, char* fname, ...){
    __CrownUInt(x, cnt_sym_var, ln, fname);
}

void __CrownULongInit(unsigned long* x, unsigned long val, int cnt_sym_var, int ln, char* fname, ...){
    __CrownULong(x, cnt_sym_var, ln, fname);
}

void __CrownULongLongInit(unsigned long long* x, unsigned long long val, int cnt_sym_var, int ln, char* fname, ...){
    __CrownULongLong(x, cnt_sym_var, ln, fname);
}

void __CrownCharInit(char* x, char val, int cnt_sym_var, int ln, char* fname, ...){
    __CrownChar(x, cnt_sym_var, ln, fname);
}

void __CrownShortInit(short* x, short val, int cnt_sym_var, int ln, char* fname, ...){
    __CrownShort(x, cnt_sym_var, ln, fname);
}

void __CrownIntInit(int* x, int val, int cnt_sym_var, int ln, char* fname, ...){
    __CrownInt(x, cnt_sym_var, ln, fname);
}

void __CrownLongInit(long * x, long val, int cnt_sym_var, int ln, char* fname, ...){
    __CrownLong(x, cnt_sym_var, ln, fname);
}

void __CrownLongLongInit(long long * x, long long val, int cnt_sym_var, int ln, char* fname, ...){
    __CrownLongLong(x, cnt_sym_var, ln, fname);
}

void __CrownFloatInit(float * x, float val, int cnt_sym_var, int ln, char* fname, ...){
    __CrownFloat(x, cnt_sym_var, ln, fname);
}

void __CrownDoubleInit(double * x, double val, int cnt_sym_var, int ln, char* fname, ...){
    __CrownDouble(x, cnt_sym_var, ln, fname);
}

void __CrownLongDoubleInit(long double * x, long double val, int cnt_sym_var, int ln, char* fname, ...){
    __CrownLongDouble(x, cnt_sym_var, ln, fname);
}

void __CrownLongDouble(long double *x, int cnt_sym_var, int ln, char* fname, ...)
{
    puts("crown_replay: CROWN_longdouble() is not supported yet ");
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
