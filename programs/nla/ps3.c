#include <stdio.h>
#include <assert.h>
int mainQ(int k){
     int y = 0;
     int x = 0;
     int c = 0;

     printf("x y k\n");
     while(1){
	  //assert(6*x-2*y*y*y-3*y*y-y == 0);	  
	  //%%%traces: int x, int y, int k
	  printf("%d %d %d\n",x, y, k);
	  if (!(c < k)) break;    
	  c = c +1 ;
	  y=y +1;
	  x=y*y+x;
     }
     return x;
}



int main(int argc, char **argv){
     mainQ(atoi(argv[1]));
     return 0;
}

