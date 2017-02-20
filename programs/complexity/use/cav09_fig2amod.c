#include <stdio.h>
#include <assert.h>

int mainQ(int n, int m){
     assert (m > 0);
     assert (n > m);
     
     int x = 0;
     int y = 0;
     int t = 0;
     while(x < n){
	  if(y < m){
	       y++;
	  }
	  else{
	       y=0;
	       x++;
	  }
	  t++;
	  
     }
     //want to know relation between counter t and inputs n,m
     //dig2: m*n + n - t == 0   (n*(m+1))
     //%%%traces: int n, int m, int t
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
