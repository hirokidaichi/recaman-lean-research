// Claim SM: last clock endable from 0  =>  for all q in (0,n): slack(q,n) <= slack(0,n).
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){int n=atoi(argv[1]); long viol=0,tot=0; int F[64],G[64]; int hist[8][8]={{0}};
 for(long m=0;m<(1L<<n);m++){ int s[64]; for(int i=0;i<n;i++) s[i]=((m>>i)&1)?1:-1;
  if(s[n-1]<0) continue;
  F[0]=0;G[0]=0; for(int i=0;i<n;i++)F[i+1]=F[i]+s[i]; for(int u=1;u<=n;u++)G[u]=G[u-1]+F[u];
  int tau[64]; for(int b=0;b<n;b++){tau[b]=-1; if(s[b]<0)continue; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]){tau[b]=t;break;}}
  if(tau[n-1]<0) continue; tot++;
  // slack(q,n) = #S[q,n) - #{b in [q,n): tau_b >= q}
  int S0=0,e0=0; for(int b=0;b<n;b++){ if(s[b]<0)S0++; else if(tau[b]>=0)e0++; }
  int sl0=S0-e0, mx=-99,mq=-1;
  for(int q=1;q<n;q++){ int Sq=0,eq=0; for(int b=q;b<n;b++){ if(s[b]<0)Sq++; else if(tau[b]>=q)eq++; } if(Sq-eq>mx){mx=Sq-eq;mq=q;} }
  if(sl0<8&&mx-sl0>=0&&mx-sl0<8) hist[sl0][mx-sl0>7?7:mx-sl0]++;
  if(mx>sl0){ viol++; if(mx>2*sl0){ for(int i=0;i<n;i++)putchar(s[i]>0?'A':'S'); printf(" slack0=%d maxsuffix=%d at q=%d\n",sl0,mx,mq);} } }
 printf("n=%d tot=%ld viol=%ld\n",n,tot,viol); for(int a=0;a<6;a++){printf("slack0=%d:",a); for(int c=0;c<8;c++)printf(" %d",hist[a][c]); printf("\n");}}
