// TS' : prefix x=sigma[0,n), last clock A. States at q=n for each start t: D=F(n)-F(t), Ar=sum_{u=t+1}^{n}(F(u)-F(t)).
// t1: (j+1, -j(j+1)/2); t2: (i+j, -(i+j)(i+j-1)/2-2i-1). Report min slack(0,n) per (j,i), mode: 0 none, 1 prefix-H (slack(0,k)>=0 all k), 2 H on all subintervals
#include <stdio.h>
#include <stdlib.h>
int n,s[64],F[65],G[65];
int endab(int b,int p){ if(s[b]<0) return 0; for(int t=b-3;t>=p;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
int main(int c,char**v){n=atoi(v[1]);int mode=atoi(v[2]),part=atoi(v[3]),np=atoi(v[4]); int mins[40][40]; long cnt[40][40]; for(int a=0;a<40;a++)for(int b=0;b<40;b++){mins[a][b]=99;cnt[a][b]=0;}
 for(long m=part;m<(1L<<(n-1));m+=np){ for(int i=0;i<n-1;i++) s[i]=((m>>i)&1)?1:-1; s[n-1]=1; F[0]=G[0]=0; for(int i=0;i<n;i++){F[i+1]=F[i]+s[i];G[i+1]=G[i]+F[i+1];}
  int E[64]; for(int b=0;b<n;b++) E[b]=endab(b,0);
  int d=0,ok=1; for(int b=0;b<n;b++){ if(s[b]<0)d++; else if(E[b]) d--; if(d<0){ok=0;break;} } if(mode>=1&&!ok) continue;
  if(mode==2){ for(int p=1;p<n&&ok;p++){int dd=0; for(int b=p;b<n;b++){ if(s[b]<0)dd++; else if(endab(b,p)) dd--; if(dd<0){ok=0;break;}}} if(!ok) continue; }
  int sl=d; if(sl>=atoi(v[5])) continue;  // only interested in violations
  // states
  static char has[70][1200]; // D in [-n,n], Ar offset
  for(int t=0;t<n;t++){ int D=F[n]-F[t]; long Ar=G[n]-G[t]-(long)(n-t)*F[t]; if(D>=1&&Ar<=0&&Ar>-1000) has[D][-Ar]=1; }
  for(int j=0;j<n;j++){ int D1=j+1; int A1=j*(j+1)/2; if(D1>=70||A1>=1000||!has[D1][A1]) continue;
    for(int i=0;i+j<n;i++){ int N=i+j; if(N<1) continue; int A2=N*(N-1)/2+2*i+1; if(A2>=1000||!has[N][A2]) continue;
      cnt[j][i]++; if(sl<mins[j][i]){mins[j][i]=sl; for(int k=0;k<n;k++)putchar(s[k]>0?'A':'S'); printf(" VIOL slack=%d j=%d i=%d\n",sl,j,i);} } }
  for(int t=0;t<n;t++){ int D=F[n]-F[t]; long Ar=G[n]-G[t]-(long)(n-t)*F[t]; if(D>=1&&Ar<=0&&Ar>-1000) has[D][-Ar]=0; }
 }
 printf("n=%d mode=%d part=%d done\n",n,mode,part);}
