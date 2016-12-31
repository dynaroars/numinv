#include <stdio.h>
#include <assert.h>

int mainQ(int a){
  int n,x,y,z;

  n=0; x=0; y=1; z=6;

  printf("a n x y z\n");
  while(1){
       printf("%d %d %d %d %d\n", a, n, x, y, z);     
       if(!(n<=a)) break;
       //assert(z == 6*n + 6);
       //assert(y == 3*n*n + 3*n + 1);
       //assert(x == n*n*n);
       
       //%%%traces: int a, int n, int x, int y, int z
       
       n=n+1;
       x=x+y;
       y=y+z;
       z=z+6;
  }

  return x;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]));
     return 0;
}

