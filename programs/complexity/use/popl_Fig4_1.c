#include <stdio.h>
#include <assert.h>

int mainQ(int n, int m){
     int x = 0;
     int y = 0;
     int t = 0;
     int t1 = 0;
     int t2 = 0;
     while(x < n){
	  if(y < m){
	       y = y + 1;
	       t1++;
	  }
	  else{
	       x = x + 1;
	       t2++;
	  }
	  t++;
     }
     //want to know relation between counter t and inputs
     //%%%traces: int n, int m, int t, int t1, int t2
     //DIG: nothing useful
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
