#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work
#include <time.h>

int r2(){return rand() %2;}

int mainQ(int n, int m){
     assert (n > 0);
     assert (m > 0);
     int v1 = n;
     int v2 = 0;
     int t = 0;
     while(v1 > 0 && r2()){
	  if (v2 < m) {
	       v2++;
	       v1--;
	  }else{
	       v2=0;
	  }
	  t++;
     }

     
     //%%%traces: int n, int m, int t, int v1, int v2
     //dig2: l21: m*n - m*t + n - v2 == 0, v1 == 0
     //not really relationship btw t and m,n  (annotated n+n*m)
     return 0;
}


int main(int argc, char **argv){
     srand(time(NULL));
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
