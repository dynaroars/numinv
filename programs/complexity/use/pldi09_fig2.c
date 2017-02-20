#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work


int mainQ(int n, int m, int N){
     assert (0 <= n);
     assert (0 <= m);
     assert (0 <= N);
     int t = 0;
     int i = 0;
     int j = 0;
     int k = 0;
     while(i < n){
	  j = 0;
	  while(j<m){	       
	       j = j+1;
	       k=i;
	       t = t +1;
	       while (k<N){		    
		    k=k+1;
		    t = t +1;
	       }
	       i=k;
	  }
	  i=i+1;
	  t = t + 1;
     }
     //%%%traces: int n, int m, int N, int t
     //printf("%d %d %d %d\n",n,m,N,t);
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
     return 0;
}
