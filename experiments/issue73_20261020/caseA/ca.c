// Case-A pattern: last clock endable from 0, q0=tau[n-1]>0, Phi(q)=slack(q,n)-slack(0,n)>0 for q in (0,q0].
// Histogram slack0; print strings with slack0<=MAXP.
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){int n=atoi(argv[1]); int maxp=atoi(argv[2]); int part=argc>3?atoi(argv[3]):0, np=argc>4?atoi(argv[4]):1;
 long hist[40]={0},tot=0,printed=0;
 for(long m=part;m<(1L<<(n-1));m+=np){ int s[64],F[65],G[65],tau[64];
  for(int i=0;i<n-1;i++) s[i]=((m>>i)&1)?1:-1; s[n-1]=1;
  F[0]=0;G[0]=0; for(int i=0;i<n;i++)F[i+1]=F[i]+s[i]; for(int u=1;u<=n;u++)G[u]=G[u-1]+F[u];
  // last clock first
  int b=n-1; tau[b]=-1; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]){tau[b]=t;break;}
  if(tau[b]<=0) continue;
  for(b=0;b<n-1;b++){tau[b]=-1; if(s[b]<0)continue; for(int t=b-3;t>=0;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]){tau[b]=t;break;}}
  int th[65]={0}; for(b=0;b<n;b++) if(tau[b]>=0) th[tau[b]]++;
  // slack(q) = #S[q,n) - #{tau>=q}
  int sl[65]; int Sc=0,Ec=0; sl[n]=0; for(int q=n-1;q>=0;q--){ if(s[q]<0)Sc++; Ec+=th[q]; sl[q]=Sc-Ec; }
  int q0=tau[n-1], ok=1; for(int q=1;q<=q0;q++) if(sl[q]<=sl[0]){ok=0;break;}
  if(!ok) continue; tot++; int h=sl[0]; if(h<0)h=0; if(h>39)h=39; hist[h]++;
  if(sl[0]<=maxp && printed<200000){printed++; for(int i=0;i<n;i++)putchar(s[i]>0?'A':'S'); printf(" sl0=%d q0=%d sl:",sl[0],q0); for(int q=0;q<=n;q++)printf("%d,",sl[q]); printf("\n");}
 }
 printf("#n=%d tot=%ld hist:",n,tot); for(int i=0;i<12;i++)printf(" %ld",hist[i]); printf("\n");}
