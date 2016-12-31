#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <stdlib.h>  //required for afloat to work

int mainQ(int z, int k){
     assert(k >= 0);
     int x = 1; int y = z; int c = 1;
     printf("x y z k\n");
     while (1){
	  //assert(x*z - x - y + 1 == 0);
	  //%%%traces: int x, int y, int z, int k
	  printf("%d %d %d %d\n",x, y, z, k);
	  if(!(c < k)) break;
	  
	  c = c + 1;
	  x = x*z + 1;
	  y = y*z;

     }//geo1

     x = x *(z - 1);

     return x;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}

