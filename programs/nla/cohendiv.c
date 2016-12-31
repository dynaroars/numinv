#include <stdio.h>
#include <assert.h>
#include <stdlib.h>  //required for afloat to work

int mainQ(int x, int y){
     //Cohen's integer division
     //returns x % y

     assert(x>0 && y>0);
  
     int q=0;
     int r=x;

     //printf("x y q a b r\n"); //inner vars
     //printf("x y q r\n"); //outter vars
     while(1) {
	  //printf("%d %d %d %d\n",x,y,q,r);
	  if(!(r>=y)) break;
	  int a=1;
	  int b=y;
	  
	  while (1){
	       //assert(r>=2*y*a && b==y*a && x==q*y+r && r>=0);
	       //%%%traces: int x, int y, int q, int a, int b, int r
	       
	       //printf("%d %d %d %d %d %d\n",x,y,q,a,b,r);
	       if(!(r >= 2*b)) break;
	       
	       a = 2*a;
	       b = 2*b;
	  }
	  r=r-b;
	  q=q+a;
     }
     //assert(r == x % y);
     //assert(q == x / y);
     //assert(x == q*y+r);
     ////%%%traces: int x, int y, int q, int r
     return q;
}

int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}

