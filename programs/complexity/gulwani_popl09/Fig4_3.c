#include <stdio.h>
#include <assert.h>

int mainQ(int n, int m){
    assert(m >= 0);
    assert(n >= 0);
     int x = 0;
     int y = 0;
     int t = 0;
     while(x < n){
	  if(y < m){
	       y++;
	  }
	  else{
	       y=0;
	       x++;
	  }
	  t++;
     }



     //%%%traces: int n, int m, int y, int x, int t
     //dig2:  y <= 0, -x <= 0, n - t <= 0, -t + x <= 0, n*t - t*x == 0, -y <= 0
     //NOTE: *** does this eq  n*t - t*x == 0  give us anything useful about the complexity?  ***
     //Timos: I tried this example with DIG1 and I got m*n + n - t == 0 which looks exactly right. Is there something missing above?
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
