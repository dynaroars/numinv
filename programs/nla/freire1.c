#include <stdio.h>
#include <assert.h>

int mainQ(int a){
     float x = ((double)a)/2.0;
     int r = 0;

     //printf("a x r\n");
     while(1){
	  //assert((double)a == 2*x + r*r - r); 
	  //%%%traces: double a, double x, int r
	  //printf("%d %g %d\n", a, x, r);
	  
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

