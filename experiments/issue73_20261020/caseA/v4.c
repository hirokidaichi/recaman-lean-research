// all strings, last clock endable with q0=tau>0: table cnt[a_y][X][d] (capped 11), report max X-d and min slack0 when X>d
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){int n=atoi(argv[1]); int part=atoi(argv[2]), np=atoi(argv[3]);
 static long cnt[12][12][12]; int maxXd=-99;
 for(long m=part;m<(1L<<(n-1));m+=np){ int s[64],F[65],G[65],tau[64];
  for(int i=0;i<n-1;i++) s[i]=((m>>i)&1)?1:-1; s[n-1]=1;
  F[0]=0;G[0]=0; for(int i=0;i<n;i++)F[i+1]=F[i]+s[i]; for(int u=1;u<=n;u++)G[u]=G[u-1]+F[u];
  int b=n-1; tau[b]=-1; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]){tau[b]=t;break;}
  if(tau[b]<=0) continue; int q0=tau[b];
  for(b=0;b<n-1;b++){tau[b]=-1; if(s[b]<0)continue; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]){tau[b]=t;break;}}
  int X=0,ay=0; for(b=q0;b<n;b++){ if(s[b]>0&&tau[b]<0) ay++; if(s[b]>0&&tau[b]>=0&&tau[b]<q0) X++;}
  int d=0; for(b=0;b<q0;b++){ if(s[b]<0)d++; else if(tau[b]>=0) d--;}
  if(X-d>maxXd) maxXd=X-d;
  if(d>11)d=11; if(X>11)X=11; if(ay>11)ay=11; cnt[ay][X][d]++;
 }
 printf("#n=%d part %d/%d maxX-d=%d\n",n,part,np,maxXd);
 for(int a=0;a<12;a++)for(int X=0;X<12;X++)for(int d=0;d<12;d++) if(cnt[a][X][d]) printf("%d %d %d %ld\n",a,X,d,cnt[a][X][d]);}
