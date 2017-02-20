#include <stdio.h>
#include <assert.h>

int mainQ(int m){
     int x = 0;
     int y = 0;
     int i = 0;
     int t = 0;
     while(x < 100){
	  if (y < m){
	       y++;
	  }
	  else{
	       x++;
	  }
	  t++;
     }
     //%%%traces: int m, int x, int y, int t
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]));
     return 0;
}
