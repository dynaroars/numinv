#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work

int mainQ(int x1, int x2){
     
     assert (x1 >= 0);
     assert (x2 >= 1);
     
     int y1,y2,y3;
     y1 = 0;
     y2 = 0;
     y3 = x1;

     printf("y1 y2 y3 x1 x2\n");
     while(1) {
	  //assert(y1* x2 + y2 + y3 == x1);
	  
	  //%%%traces: int y1, int y2, int y3, int x1, int x2
	  
	  printf("%d %d %d %d %d\n",y1,y2,y3,x1,x2);
	  if(!(y3 != 0)) break;
	  
	  if (y2 + 1 == x2) {
	       y1 = y1 + 1;
	       y2 = 0;
	       y3 = y3 - 1;
	  }
	  else {
	       y2 = y2 + 1;
	       y3 = y3 - 1;
	  }
     }

     //assert(y1 == x1 / x2);
     return y1;
}

int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}

