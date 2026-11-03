// Distorted tower certificate for Erdos #273 (moduli d | L, d>=4, d+1 prime), increasing prime order.
// eta(delta) = sum_i min(M1_i, M2_i/(4 d_i (1-d_i))),  M1_i = sum_S A_i[S] prod_{p in S} c_p,
// M2_i = sum_S B_i[S] prod_{p in S} c_p, S = support (among earlier primes) of m (resp. lcm(m1,m2)).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
typedef long long ll;
static int isprime(ll n){ if(n<2) return 0; if(n%2==0) return n==2; for(ll q=3;q*q<=n;q+=2) if(n%q==0) return 0; return 1; }
static ll gcdl(ll a,ll b){ while(b){ ll t=a%b; a=b; b=t;} return a; }
#define MAXP 12
int np; ll P[MAXP]; int E[MAXP]; double U[MAXP];
static double g(int k,int v){ double a=pow((double)P[k],E[k]-v); return (a<U[k]?a:U[k])/U[k]; }
static int vp(ll n,ll p){ int v=0; while(n%p==0){n/=p;v++;} return v; }
double A[MAXP][1<<MAXP], B[MAXP][1<<MAXP];
static double eta_of(double*dl){
  double c[MAXP]; for(int k=0;k<np;k++) c[k]=1.0/(1.0-dl[k]);
  double tot=0;
  for(int i=0;i<np;i++){
    int ns=1<<i; double M1=0,M2=0;
    for(int S=0;S<ns;S++){ if(A[i][S]==0 && B[i][S]==0) continue; double pr=1; for(int k=0;k<i;k++) if(S>>k&1) pr*=c[k]; M1+=A[i][S]*pr; M2+=B[i][S]*pr; }
    double t=M1; if(dl[i]>0){ double t2=M2/(4*dl[i]*(1-dl[i])); if(t2<t) t=t2; }
    tot+=t;
  }
  return tot;
}
int ALLPERM=1;
static int next_perm(int*a,int n){ int i=n-2; while(i>=0&&a[i]>=a[i+1]) i--; if(i<0) return 0; int j=n-1; while(a[j]<=a[i]) j--; int t=a[i];a[i]=a[j];a[j]=t; for(int l=i+1,r=n-1;l<r;l++,r--){t=a[l];a[l]=a[r];a[r]=t;} return 1; }
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); ll L; int nfail=0, nall=0; double worst=0;
  FILE*out=fopen(argv[2],"w");
  while(fscanf(f,"%lld",&L)==1){
    nall++;
    ll m=L; np=0; for(ll q=2;q*q<=m;q++) if(m%q==0){ P[np]=q; E[np]=0; while(m%q==0){m/=q;E[np]++;} np++; } if(m>1){P[np]=m;E[np]=1;np++;}
    ll P0[MAXP]; int E0[MAXP]; for(int k=0;k<np;k++){P0[k]=P[k];E0[k]=E[k];}
    int perm[MAXP]; for(int k=0;k<np;k++) perm[k]=k;
    double bestAll=1e9; double bestD[MAXP]; ll bestP[MAXP]; double cur; double dl[MAXP];
    do {
    for(int k=0;k<np;k++){P[k]=P0[perm[k]];E[k]=E0[perm[k]];}
    for(int k=0;k<np;k++){ double pe=pow((double)P[k],E[k]); double rem=0; if(P[k]==2) for(int j=1;j<=E[k];j++){ ll d=1LL<<j; if(d>=4 && isprime(d+1)) rem+=pow(2.0,E[k]-j);} U[k]=pe-rem; }
    // allowed divisors
    static ll dv[100000]; int nd=1; dv[0]=1;
    for(int k=0;k<np;k++){ int cur=nd; ll pw=1; for(int e=1;e<=E[k];e++){ pw*=P[k]; for(int t=0;t<cur;t++) dv[nd++]=dv[t]*pw; } }
    memset(A,0,sizeof(A)); memset(B,0,sizeof(B));
    for(int i=0;i<np;i++){
      // mixed moduli of stage i: allowed d, p_i | d, no later prime divides d, m = d / p_i^j > 1
      static ll mm[20000]; static int jj[20000]; static double gm[20000]; int nm=0;
      for(int t=0;t<nd;t++){ ll d=dv[t]; if(d<4 || !isprime(d+1)) continue; if(d%P[i]) continue;
        int later=0; for(int k=i+1;k<np;k++) if(d%P[k]==0){later=1;break;} if(later) continue;
        int j=vp(d,P[i]); ll mpart=d; for(int r=0;r<j;r++) mpart/=P[i]; if(mpart==1) continue;
        // g-part of nu(m) (without c)
        double gp=1; for(int k=0;k<i;k++){ int v=vp(mpart,P[k]); if(v) gp*=g(k,v); }
        mm[nm]=mpart; jj[nm]=j; gm[nm]=gp; nm++; }
      for(int a=0;a<nm;a++){ int S=0; for(int k=0;k<i;k++) if(mm[a]%P[k]==0) S|=1<<k; A[i][S]+=g(i,jj[a])*gm[a]; }
      for(int a=0;a<nm;a++) for(int b=0;b<nm;b++){
        ll l=mm[a]/gcdl(mm[a],mm[b])*mm[b]; int S=0; double gp=1;
        for(int k=0;k<i;k++){ int v=vp(l,P[k]); if(v){ S|=1<<k; gp*=g(k,v);} }
        B[i][S]+=g(i,jj[a])*g(i,jj[b])*gp; }
    }
    for(int k=0;k<MAXP;k++) dl[k]=0; cur=eta_of(dl); int imp=1;
    while(imp){ imp=0; for(int i=1;i<np;i++) for(int s=0;s<=100;s++){ double save=dl[i]; dl[i]=s/200.0; double v=eta_of(dl); if(v<cur-1e-13){cur=v;imp=1;} else dl[i]=save; } }
    if(cur<bestAll){bestAll=cur; for(int k=0;k<np;k++){bestD[k]=dl[k];bestP[k]=P[k];}}
    if(bestAll<1 && !ALLPERM) break;
    } while(ALLPERM && next_perm(perm,np));
    cur=bestAll; for(int k=0;k<np;k++){dl[k]=bestD[k];P[k]=bestP[k];}
    if(cur>worst && cur<1) worst=cur;
    fprintf(out,"%lld %.9f",L,cur); for(int k=0;k<np;k++) fprintf(out," %lld:%d",P[k],(int)llround(dl[k]*200)); fprintf(out,"\n");
    if(cur>=1){ nfail++; if(nfail<=15) printf("NOT EXCLUDED L=%lld eta=%.4f\n",L,cur); }
  }
  printf("candidates=%d not excluded=%d worst excluded eta=%.6f\n",nall,nfail,worst);
}
