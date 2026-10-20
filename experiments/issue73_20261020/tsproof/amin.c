// min over prefixes (last A, prefix-H) of area(t,q] + D(D-1)/2  per slack s and D=F(q)-F(t)>=1 ; also count starts with area<=-D(D-1)/2
#include <stdio.h>
#include <stdlib.h>
int n,s[64],F[65],G[65];
int endab(int b,int p){ if(s[b]<0) return 0; for(int t=b-3;t>=p;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
int main(int c,char**v){n=atoi(v[1]); int mn[6][40]; int maxbad[6]; for(int a=0;a<6;a++){maxbad[a]=0;for(int b=0;b<40;b++)mn[a][b]=999;}
 for(long m=0;m<(1L<<(n-1));m++){ for(int i=0;i<n-1;i++) s[i]=((m>>i)&1)?1:-1; s[n-1]=1; F[0]=G[0]=0; for(int i=0;i<n;i++){F[i+1]=F[i]+s[i];G[i+1]=G[i]+F[i+1];}
  int d=0,ok=1; for(int b=0;b<n;b++){ if(s[b]<0)d++; else if(endab(b,0)) d--; if(d<0){ok=0;break;} } if(!ok||d>5) continue;
  int bad=0;
  for(int t=0;t<n;t++){ int D=F[n]-F[t]; if(D<1) continue; long Ar=G[n]-G[t]-(long)(n-t)*F[t]; int val=Ar+D*(D-1)/2; if(val<mn[d][D]) mn[d][D]=val; if(val<=0) bad++; }
  if(bad>maxbad[d]){maxbad[d]=bad; for(int k=0;k<n;k++)putchar(s[k]>0?'A':'S'); printf(" s=%d bad=%d\n",d,bad);}
 }
 for(int a=0;a<6;a++){printf("s=%d:",a); for(int D=1;D<15;D++) printf(" %d",mn[a][D]==999?99:mn[a][D]); printf("\n");}}
