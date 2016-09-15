#include <stdio.h>
#include <assert.h>
//#include <stdlib.h>  //required for afloat to work

int mainQ(int a){
     double da = (int)a;
     float x = da/2.0;
     int r = 0;
     while(1){
	  assert(da == 2*x + r*r - r); 
	  //%%%traces: double a, double x, int r
	  //printf("l0: da x r\n");
	  //printf("l0: %f %f %f\n",da,x,r);
	  if (!(x>r)) break;
	  x = x - r; r = r + 1;
     }

     //assert(r==(int)round(sqrt(a)));
     return r;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]));
     return 0;
}

