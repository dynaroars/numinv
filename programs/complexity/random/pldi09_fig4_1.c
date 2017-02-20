#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work
#include <time.h>

int r2(){return rand() %2;}

int mainQ(int id, int n){
     assert (id >= 0);
     assert (n > id);
     int tmp = id + 1;
     int t = 0;

     while(tmp != id && r2()){
	  if (tmp <= n) {
	       tmp = tmp + 1;
	  }else{
	       tmp=0;
	  }
	  t++;
     }
     //%%%traces: int id, int n, int t
     //printf("%d, %d, %d\n", id, n, t);
     //dig2: n - t + 1 == 0
     return 0;
}


int main(int argc, char **argv){
     srand(time(NULL));
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
