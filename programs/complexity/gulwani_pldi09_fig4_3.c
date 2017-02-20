#include <stdio.h>
#include <assert.h>
//same as fig2a gulwani_cav09


int mainQ(int n, int m){
     assert (m > 0);
     assert (n > m);
     int i = 0;
     int j = 0;
     int t = 0;
     while(1){
	  if (!(i<n)) break;
	  if (j < m) {
	       j++;
	  }else{
	       j=0;
	       i++;
	  }
	  t++;
     }
     //%%%traces: int n, int m, int t, int i, int j
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
