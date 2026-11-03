// Local search for counterexamples to WOWII conjectures (n <= 22), invariants as in formal-conjectures.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
typedef unsigned U;
static int n; static U adj[32];
static int pc(U x){return __builtin_popcount(x);}
static int ctz(U x){return __builtin_ctz(x);}
static int D[32][32];
static void bfs_all(void){ for(int v=0;v<n;v++){ for(int w=0;w<n;w++) D[v][w]=-1; D[v][v]=0; U fr=1u<<v, seen=fr; int d=0;
  while(fr){ U nb=0; for(U m=fr;m;m&=m-1) nb|=adj[ctz(m)]; nb&=~seen; d++; for(U m=nb;m;m&=m-1) D[v][ctz(m)]=d; seen|=nb; fr=nb; } } }
static int connected_sub(U S){ if(!S) return 0; U seen=S&-S, fr=seen; while(fr){U nb=0; for(U m=fr;m;m&=m-1) nb|=adj[ctz(m)]; nb&=S&~seen; seen|=nb; fr=nb;} return seen==S; }
static int edges_in(U S){ int t=0; for(U m=S;m;m&=m-1) t+=pc(adj[ctz(m)]&S); return t/2; }
static int alpha_of(U S){ if(!S) return 0; // pick max degree vertex in S
  int best=-1,bd=-1; for(U m=S;m;m&=m-1){int v=ctz(m), d=pc(adj[v]&S); if(d>bd){bd=d;best=v;}}
  if(bd==0) return pc(S);
  if(bd<=1){ // matching-ish: handle degree-0/1 greedily: take a leaf
    for(U m=S;m;m&=m-1){int v=ctz(m); if(pc(adj[v]&S)==1) return 1+alpha_of(S&~(1u<<v)&~adj[v]);} }
  int v=best; int a=alpha_of(S&~(1u<<v)); int b=1+alpha_of(S&~(1u<<v)&~adj[v]); return a>b?a:b; }
static int ecc(int v){int m=0; for(int w=0;w<n;w++) if(D[v][w]>m) m=D[v][w]; return m;}
static int rad(void){int r=99; for(int v=0;v<n;v++){int e=ecc(v); if(e<r) r=e;} return r;}
static int diam(void){int r=0; for(int v=0;v<n;v++){int e=ecc(v); if(e>r) r=e;} return r;}
static double avgecc(void){double s=0; for(int v=0;v<n;v++) s+=ecc(v); return s/n;}
static int lv(int v){return alpha_of(adj[v]);}
static int maxL(void){int m=0; for(int v=0;v<n;v++){int x=lv(v); if(x>m)m=x;} return m;}
static double avgL(void){double s=0; for(int v=0;v<n;v++) s+=lv(v); return s/n;}
static int distEven(int v){int c=0; for(int w=0;w<n;w++) if(D[v][w]%2==0) c++; return c;}
static int mindeg(void){int m=99; for(int v=0;v<n;v++) if(pc(adj[v])<m) m=pc(adj[v]); return m;}
static int sigma2(void){int d[32]; for(int v=0;v<n;v++) d[v]=pc(adj[v]); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(d[j]<d[i]){int t=d[i];d[i]=d[j];d[j]=t;} return n>1?d[1]:0;}
static int has_c4(void){ for(int a=0;a<n;a++) for(int c=a+1;c<n;c++) if(pc(adj[a]&adj[c]&~(1u<<a)&~(1u<<c))>=2) return 1; return 0; }
// largest induced forest: branch on vertices with union-find feasibility (acyclic check incremental)
static int best_f; static int uf[32];
static int fnd(int x,int*p){while(p[x]!=x) x=p[x]; return x;}
static void forest_rec(int i, U S, int sz, int *par){
  if(sz + (n-i) <= best_f) return;
  if(i==n){ if(sz>best_f) best_f=sz; return; }
  // try include i
  int p2[32]; memcpy(p2,par,sizeof(int)*n); int ok=1;
  for(U m=adj[i]&S;m;m&=m-1){int u=ctz(m); int a=fnd(u,p2), b=fnd(i,p2); if(a==b){ok=0;break;} p2[a]=b;}
  if(ok) forest_rec(i+1, S|(1u<<i), sz+1, p2);
  forest_rec(i+1, S, sz, par);
}
static int forest(void){ best_f=0; int p[32]; for(int i=0;i<n;i++) p[i]=i; forest_rec(0,0,0,p); return best_f; }
// largest induced bipartite: branch with colors
static int best_b; static int col[32];
static void bip_rec(int i, U A, U B, int sz){
  if(sz+(n-i)<=best_b) return;
  if(i==n){ if(sz>best_b) best_b=sz; return;}
  if(!(adj[i]&A)) bip_rec(i+1, A|(1u<<i), B, sz+1);
  if(!(adj[i]&B) && A) bip_rec(i+1, A, B|(1u<<i), sz+1);
  bip_rec(i+1, A, B, sz);
}
static int bip(void){ best_b=0; bip_rec(0,0,0,0); return best_b; }
// largest induced tree: grow connected acyclic sets from each start (ordered to avoid huge dup is hard; use branch with frontier)
static int best_t;
static void tree_rec(U S, U cand, U excl){
  int sz=pc(S); if(sz>best_t) best_t=sz;
  if(sz+pc(cand)<=best_t && 0) return;
  // upper bound: sz + |vertices reachable not excluded|
  U avail=~(S|excl)&((n==32)?~0u:((1u<<n)-1));
  if(sz+pc(avail)<=best_t) return;
  if(!cand) return;
  int v=ctz(cand);
  // include v if it has exactly one neighbor in S
  if(pc(adj[v]&S)==1){ U S2=S|(1u<<v); U c2=(cand|adj[v])&~S2&~excl; // drop candidates with >=2 nbrs in S2
     U c3=0; for(U m=c2;m;m&=m-1){int u=ctz(m); if(pc(adj[u]&S2)==1) c3|=1u<<u;} tree_rec(S2,c3,excl); }
  tree_rec(S, cand&~(1u<<v), excl|(1u<<v));
}
static int tree(void){ best_t=1; U ex=0; for(int r=0;r<n;r++){ tree_rec(1u<<r, adj[r]&~ex, ex); ex|=1u<<r; } return best_t; }
// largest induced path
static int best_p;
static void path_rec(int end, U S, int len, int start){
  if(len>best_p) best_p=len;
  for(U m=adj[end]&~S;m;m&=m-1){int w=ctz(m); // w adjacent only to end within S
    if((adj[w]&S)==(1u<<end)) path_rec(w, S|(1u<<w), len+1, start);}
}
static int ipath(void){ best_p=1; for(int v=0;v<n;v++) path_rec(v,1u<<v,1,v); return best_p; }
// Hamiltonian path DP
static unsigned char *hp; static int hamp(void){ U full=(n==32)?~0u:((1u<<n)-1); size_t N=1ul<<n; if(!hp) hp=malloc(1ul<<22);
  U *dp=(U*)calloc(N,sizeof(U)); for(int v=0;v<n;v++) dp[1u<<v]=1u<<v;
  for(U S=1;S<=full;S++){U e=dp[S]; if(!e) continue; for(U m=e;m;m&=m-1){int v=ctz(m); for(U k=adj[v]&~S;k;k&=k-1){int w=ctz(k); dp[S|(1u<<w)]|=1u<<w;}} if(S==full) break;}
  int r=dp[full]!=0; free(dp); return r; }
static int kappa(void){ if(n<=1) return 0; U full=(1u<<n)-1; for(int k=0;k<n-1;k++){ // subsets of size k
    for(U S=0;S<=full;S++){ if(pc(S)!=k) continue; if(!connected_sub(full&~S)) return k; } } return n-1; }
static int residue(void){ int d[32],m=n; for(int v=0;v<n;v++) d[v]=pc(adj[v]);
  while(m>0){ for(int i=0;i<m;i++) for(int j=i+1;j<m;j++) if(d[j]>d[i]){int t=d[i];d[i]=d[j];d[j]=t;}
    if(d[0]==0) return m; int k=d[0]; for(int i=1;i<=k && i<m;i++) d[i]--; for(int i=0;i<m-1;i++) d[i]=d[i+1]; m--; } return 0; }
static int pathcover(void){ U full=(1u<<n)-1; size_t N=1ul<<n;
  U *dp=calloc(N,sizeof(U)); for(int v=0;v<n;v++) dp[1u<<v]=1u<<v;
  for(U S=1;S<=full;S++){U e=dp[S]; if(!e) continue; for(U m=e;m;m&=m-1){int v=ctz(m); for(U k=adj[v]&~S;k;k&=k-1){int w=ctz(k); dp[S|(1u<<w)]|=1u<<w;}} if(S==full) break;}
  int *best=malloc(sizeof(int)*N); best[0]=0;
  for(U S=1;S<=full;S++){ U low=S&-S; int b=99; for(U sub=S;sub;sub=(sub-1)&S) if((sub&low)&&dp[sub]){int c=1+best[S&~sub]; if(c<b)b=c;} best[S]=b; if(S==full) break;}
  int r=best[full]; free(dp); free(best); return r; }
// slack: RHS - LHS (negative => counterexample)
static double slack(int c){
  bfs_all();
  switch(c){
   case 19: return bip() - floor(avgecc()+maxL()+1e-12);
   case 40: return forest() - ceil((pathcover()+bip()+1)/2.0-1e-12);
   case 61: return forest() - (residue()+ceil(diam()/3.0-1e-12));
   case 72: return tree() - ceil(avgecc()+maxL()/3.0-1e-12);
   case 84: return tree() - 2.0*rad()/mindeg();
   case 96: { int me=99; for(int v=0;v<n;v++){int x=distEven(v); if(x<me) me=x;} return 1.0+me*(maxL()-1) - alpha_of((1u<<n)-1); }
   case 133: return ipath() - (rad() + (has_c4()?1.0:avgL()));
   case 189: { int me=0; for(int v=0;v<n;v++){int x=distEven(v); if(x>me) me=x;} if(me>1+sigma2()) return 1.0+(me-1-sigma2()); return hamp()?1.0:-1.0; }
   case 199: { int t=tree(); int k=kappa(); int lhs=t>=2?t-2:0; if(lhs>k) return 1.0+(lhs-k); return hamp()?1.0:-1.0; }
  }
  return 0;
}
static int is_conn(void){ return connected_sub((1u<<n)-1); }
static unsigned long long rs=88172645463325252ULL; static unsigned long long rnd(void){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
#ifdef EXH
int main(int argc,char**argv){ int cs[]={19,40,61,72,84,96,133,189,199}; long cnt=0, fail[9]={0};
  while(scanf("%d",&n)==1){ for(int v=0;v<n;v++) if(scanf("%u",&adj[v])!=1) return 1; cnt++;
    for(int i=0;i<9;i++){ double s=slack(cs[i]); if(s<-1e-9){ if(fail[i]<3){printf("FAIL conj %d n=%d:",cs[i],n); for(int v=0;v<n;v++) printf(" %u",adj[v]); printf(" slack %.4f\n",s);} fail[i]++; } } }
  printf("checked %ld graphs;",cnt); for(int i=0;i<9;i++) printf(" %d:%ld",cs[i],fail[i]); printf("\n"); }
#elif defined(VAL)
int main(void){ while(scanf("%d",&n)==1){ for(int v=0;v<n;v++) scanf("%u",&adj[v]); bfs_all();
  printf("%d %d %d %d %d %d %d %d %d %d %d\n", alpha_of((1u<<n)-1), bip(), forest(), tree(), ipath(), kappa(), residue(), hamp(), rad(), diam(), maxL()); } }
#else
int main(int argc,char**argv){
  int c=atoi(argv[1]); int nmin=atoi(argv[2]), nmax=atoi(argv[3]); long iters=atol(argv[4]); rs^=(unsigned long long)atol(argv[5])*2654435761u;
  double gbest=1e9;
  for(long rep=0;;rep++){
    n=nmin+rnd()%(nmax-nmin+1);
    double p=0.15+0.5*(rnd()%1000)/1000.0;
    do{ memset(adj,0,sizeof adj); for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if((rnd()%1000)<p*1000){adj[i]|=1u<<j;adj[j]|=1u<<i;} }while(!is_conn());
    double cur=slack(c); double T=0.6;
    for(long it=0;it<iters;it++){
      int i=rnd()%n, j=rnd()%n; if(i==j) continue;
      adj[i]^=1u<<j; adj[j]^=1u<<i;
      if(!is_conn()){ adj[i]^=1u<<j; adj[j]^=1u<<i; continue; }
      double s=slack(c);
      if(s<=cur || exp((cur-s)/T) > (rnd()%100000)/100000.0) cur=s; else { adj[i]^=1u<<j; adj[j]^=1u<<i; }
      T*=0.999;
      if(cur<gbest){ gbest=cur; fprintf(stderr,"conj %d rep %ld n=%d best slack %.4f\n",c,rep,n,gbest); }
      if(cur<0){ printf("COUNTEREXAMPLE conj %d n=%d slack %.4f\n",c,n,cur); for(int v=0;v<n;v++) printf("%u ",adj[v]); printf("\n"); fflush(stdout); return 0; }
    }
    if(rep%20==0) fprintf(stderr,"rep %ld done, global best %.4f\n",rep,gbest);
  }
}
#endif
