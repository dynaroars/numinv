#include <stdio.h>
#include <assert.h>

int mainQ(int a){
     double da = (double)a;
     float x = da/2.0;
     int r = 0;
     while(1){
	  //assert(da == 2*x + r*r - r); 
	  //%%%traces: double da, double x, int r
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

