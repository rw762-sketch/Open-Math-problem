// For all L <= X: D(L) = sum_{d | L, d >= 4, d+1 prime} 1/d. Print L with D(L) >= 1.
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){
  long X=atol(argv[1]);
  char*comp=calloc(X+2,1);
  for(long i=2;i*i<=X+1;i++) if(!comp[i]) for(long j=i*i;j<=X+1;j+=i) comp[j]=1;
  float*D=calloc(X+1,sizeof(float));
  for(long d=4; d<=X; d++) if(!comp[d+1]) { float w=1.0f/d; for(long m=d;m<=X;m+=d) D[m]+=w; }
  long cnt=0; for(long L=1;L<=X;L++) if(D[L]>=0.9999f){ cnt++; if(cnt<=5) printf("%ld %.5f\n",L,D[L]); }
  printf("X=%ld candidates with D>=1: %ld\n",X,cnt);
  FILE*f=fopen(argv[2],"w"); for(long L=1;L<=X;L++) if(D[L]>=0.9999f) fprintf(f,"%ld\n",L); fclose(f);
}
