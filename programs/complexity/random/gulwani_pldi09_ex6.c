#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work
#include <time.h>

int r2(){return rand() %2;}

int mainQ(int n, int m){
     assert (0 <= n);
     assert (0 <= m);
     int i = 0;
     int j = 0;
     int k = 0;
     int t = 0;

     while(i++ < n){
	  if (r2()){
	       while(j++ < m){t++;}
	  }
	  else{
	       while(k++ < m){t++;}
	  }
     }
     //%%%traces: int n, int m, int t
     //dig2: 2*(m*m)*n - 3*m*n*t + n*(t*t) == 0, 2*(m*m)*t - 3*m*(t*t) + (t*t*t) == 0
     //int i, int j, int k
     //printf("%d %d %d %d %d\n",n,m,t,j,k);
     return 0;
}


int main(int argc, char **argv){
     srand(time(NULL));
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
