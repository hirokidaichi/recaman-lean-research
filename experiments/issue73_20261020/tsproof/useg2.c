// prefixes x (last A, prefix-H, slack s<=2) having a t1-state for some j (mode 1) or t2-state for some (j,i) with j+i>=1 (mode 2).
// print u = x[k1..n) with k1 = last zero of d, plus s, j(,i), t relative to k1
#include <stdio.h>
#include <stdlib.h>
int n,s[64],F[65],G[65];
int endab(int b,int p){ if(s[b]<0) return 0; for(int t=b-3;t>=p;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
int main(int c,char**v){n=atoi(v[1]); int mode=atoi(v[2]);
 for(long m=0;m<(1L<<(n-1));m++){ for(int i=0;i<n-1;i++) s[i]=((m>>i)&1)?1:-1; s[n-1]=1; F[0]=G[0]=0; for(int i=0;i<n;i++){F[i+1]=F[i]+s[i];G[i+1]=G[i]+F[i+1];}
  int d=0,ok=1,k1=0; for(int b=0;b<n;b++){ if(s[b]<0)d++; else if(endab(b,0)) d--; if(d<0){ok=0;break;} if(d==0) k1=b+1;} if(!ok||d>2||d<1) continue;
  if(s[k1]>0) continue; // want u to start at k1 exactly with S (it does)
  for(int t=0;t<n;t++){ int D=F[n]-F[t]; if(D<1) continue; long Ar=G[n]-G[t]-(long)(n-t)*F[t];
    if(mode==1){ int j=D-1; if(Ar==-(long)j*(j+1)/2){ printf("s=%d j=%d t-k1=%d u=",d,j,t-k1); for(int k=k1;k<n;k++)putchar(s[k]>0?'A':'S'); printf("\n"); } }
    else { int N=D; for(int i=0;i<=N;i++){int j=N-i; if(i==0 && 0) ; if(Ar==-(long)N*(N-1)/2-2*i-1){ printf("x=");for(int k=0;k<n;k++)putchar(s[k]>0?65:83);printf(" s=%d j=%d i=%d t-k1=%d u=",d,j,i,t-k1); for(int k=k1;k<n;k++)putchar(s[k]>0?'A':'S'); printf("\n"); }} }
  }
 }}
