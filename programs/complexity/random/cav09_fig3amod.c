#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <time.h>
//I think this is the same as fig2a gulwani_cav09 but use nested loop

int r2(){return rand() %2;}

int mainQ(int n){
     int x = 0;
     int y = 0;
     int t = 0;
     while(x < n && r2()){
	  y = x;
	  while (y < n && r2()){
	       t++;
	       y++;
	  }
	  
	  x=y+1;
     }
     //%%%traces: int n, int t
     //dig2:  n*t - (t*t) == 0
     //printf("%d, %d, %d, %d\n", n, t, x, y);
     return 0;
}


int main(int argc, char **argv){
     srand(time(NULL));
     mainQ(atoi(argv[1]));
     return 0;
}
