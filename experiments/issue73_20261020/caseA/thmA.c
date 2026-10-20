// Theorem A* check: all strings x of length n (p=0), last clock c=n-1 endable, q0=tau_c (newest start, q0>=0).
// a_y = #A in [q0,n) not endable from 0; d = #S[0,q0) - #endable-from-0 in [0,q0).
// Claim: a_y + d <= 2  ==>  y = sigma[q0,n) = SAAA.  Also report triples (a_y,X,d) with a_y+d<=2.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc,char**argv){int n=atoi(argv[1]); int part=argc>2?atoi(argv[2]):0, np=argc>3?atoi(argv[3]):1;
 long viol=0, good=0, tri[3][12][3]; memset(tri,0,sizeof tri);
 for(long m=part;m<(1L<<(n-1));m+=np){ int s[64],F[65],G[65],tau[64];
  for(int i=0;i<n-1;i++) s[i]=((m>>i)&1)?1:-1; s[n-1]=1;
  F[0]=0;G[0]=0; for(int i=0;i<n;i++)F[i+1]=F[i]+s[i]; for(int u=1;u<=n;u++)G[u]=G[u-1]+F[u];
  int b=n-1; tau[b]=-1; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]){tau[b]=t;break;}
  if(tau[b]<0) continue; int q0=tau[b];
  for(b=0;b<n-1;b++){tau[b]=-1; if(s[b]<0)continue; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]){tau[b]=t;break;}}
  int X=0,ay=0; for(b=q0;b<n;b++){ if(s[b]>0&&tau[b]<0) ay++; if(s[b]>0&&tau[b]>=0&&tau[b]<q0) X++;}
  int d=0; for(b=0;b<q0;b++){ if(s[b]<0)d++; else if(tau[b]>=0) d--;}
  if(ay+d>2) continue;
  int isS = (n-q0==4 && s[q0]<0 && s[q0+1]>0 && s[q0+2]>0);
  if(!isS){ viol++; if(viol<5){for(int i=0;i<n;i++){if(i==q0)putchar('|');putchar(s[i]>0?'A':'S');} printf(" VIOL a=%d X=%d d=%d\n",ay,X,d);} }
  else good++;
  if(d>=0&&d<=2&&ay<=2) tri[ay][X>11?11:X][d]++;
 }
 printf("n=%d part %d/%d: a_y+d<=2 cases=%ld violations=%ld ; triples:",n,part,np,good+viol,viol);
 for(int a=0;a<3;a++)for(int X=0;X<12;X++)for(int d=0;d<3;d++) if(tri[a][X][d]) printf(" (a%d,X%d,d%d):%ld",a,X,d,tri[a][X][d]); printf("\n");}
