#include <stdio.h>
#include <assert.h>

int mainQ(int x0, int z0, int n){
     int x = x0;
     int z = z0;
     int t = 0;
     while(x < n){
	  if(z > x){
	       x++;
	  }
	  else{
	       z++;
	  }
	  t++;
     }
     //want to know relation between counter t and inputs
     //%%%traces: int n, int x0, int z0, int t
     
     //sage: e2
     //2*n^2*t - 3*n*t^2 + t^3 - 3*n*t*x0 + 2*t^2*x0 + t*x0^2 - n*t*z0 + t^2*z0 + t*x0*z0 == 0
     //sage: solve(e2,t)
     //[t == 2*n - x0 - z0, t == n - x0, t == 0]

     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
     return 0;
}
