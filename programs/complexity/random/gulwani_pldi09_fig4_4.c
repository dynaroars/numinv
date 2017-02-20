#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work
#include <time.h>

int r2(){return rand() %2;}

int mainQ(int n, int m){
     assert (m > 0);
     assert (n > m);
     int i = n;
     int t = 0;
     while(i>0 && r2()){
	  if (i < m) {
	       i--;
	  }else{
	       i = i-m;
	  }
	  t++;
     }
     //%%%traces: int n, int m, int t, int i
     //dig2: cannot get anything useful 
     return 0;
}


int main(int argc, char **argv){
     srand(time(NULL));     
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
