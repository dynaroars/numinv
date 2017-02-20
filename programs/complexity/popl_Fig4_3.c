#include <stdio.h>
#include <assert.h>

int mainQ(int n, int m){
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

     //16:58:46:alg:Info:*** programs/complexity/popl_Fig4_2.c, 2 locs, invs 10, inps 10847, time 157.343590975 s, rand 80: 
//l17: -t <= 0, m*y - (y*y) - m*y0 + y*y0 == 0, -y + y0 <= 0, t - x + x0 == 0, n - x <= 0, n*y - x*y - n*y0 + x*y0 == 0, n*x - (x*x) - n*x0 + x*x0 == 0
//l18: -t <= 0, n*t - t*x == 0, n - x <= 0

     
     //want to know relation between counter t and inputs
     //%%%traces: int n, int m, int y, int x, int t
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
