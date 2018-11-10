// SYM_assume() to give constraints on symbolic variables.  
#include <stdio.h>
#include <assert.h>
#include <crown.h>

void main() {
   int x, y;
   SYM_int_init(x, 2);
   SYM_int(y);
   printf("x=%d, y=%d\n", x, y);
   SYM_assume( x + y > -1);
   //assert( x + y >-5 );
   int i;
   for(i=0; i < x && x < 10; i++);
} 
 

