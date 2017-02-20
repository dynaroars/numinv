#include <stdio.h>
#include <assert.h>

int mainQ(int m){

     int x = 0;
     int y = 0;
     int t = 0;
     while(x < 100){
	  if (y < m){
	       t++;
	       y++;
	  }
	  else{
	       t++;
	       x++;
	  }
     }

     //dig2: m*t - (t*t) - 100*m + 200*t - 10000 == 0
     //[t == m + 100, t == 100]

//16:12:33:alg:Info:*** programs/complexity/use/cav09_fig1mod.c, 1 locs, invs 1, inps 204, time 14.2175781727 s, rand 26: 

     
     //%%%traces: int m, int t
     //printf("%d %d\n",m,t);
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]));
     return 0;
}
