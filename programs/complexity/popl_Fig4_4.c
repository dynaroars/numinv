#include <stdio.h>
#include <assert.h>

int mainQ(int n, int m){
     int x = 0;
     int y = 0;
     int t = 0;
     while(x < n){
	  y=0;
	  x++;
	  while(y < m){
	       y++;
	  }
	  t++;
     }
     //want to know relation between counter t and inputs
     //%%%traces: int n, int m, int t
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
