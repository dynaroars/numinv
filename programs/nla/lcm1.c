#include <stdio.h>
#include <assert.h>

int mainQ(int a, int b){
     assert(a>=1);
     assert(b>=1);
     int x,y,u,v;

     x=a;
     y=b;
     u=b;
     v=0;

     printf("a b x y u v\n");     
     while(1) {
	  printf("%d %d %d %d %d %d\n",a, b, x, y, u, v);
	  if (!(x!=y)) break;
	  
	  //assert(x*u + y*v == a*b);
	  //%%%traces: int a, int b, int x, int y, int u, int v

	  while (1){
	       //printf("%d %d %d %d %d %d\n",a, b, x, y, u, v);
	       if(!(x>y)) break;
	       x=x-y;
	       v=v+u;
	  }
    
	  while (1){
	       //printf("%d %d %d %d %d %d\n",a, b, x, y, u, v);
	       if(!(x<y)) break;
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

