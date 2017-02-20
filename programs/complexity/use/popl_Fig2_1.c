#include <stdio.h>
#include <assert.h>

int mainQ(int x0, int y0, int n, int m){
     int x = x0;
     int y = y0;
     int t = 0;
     while(x < n){
	  if(y < m){
	       y++;
	  }
	  else{
	       x++;
	  }
	  t++;
     }
     //want to know relation between counter t and inputs
     //%%%traces: int n, int m, int x0, int y0, int t
     //DIG: no result -- cannot solve equations
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
     return 0;
}
