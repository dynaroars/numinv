#include <stdio.h>
#include <assert.h>

int mainQ(int a, int b){
     assert(a>0);
     assert(b>0);
     int x,y,u,v;

     x=a;
     y=b;
     u=b;
     v=0;

     int ctr = 0;
     while(x!=y) {
	  //assert(x*u + y*v == a*b);
	  //%%%traces: int a, int b, int x, int y, int u, int v

	  while (x>y){
	       x=x-y;
	       v=v+u;
	  }
    
	  while (x<y){
	       y=y-x;
	       u=u+v;
	  }

     }

     //x==gcd(a,b)
     int r = u+v; 
     return r; //lcm     
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}

