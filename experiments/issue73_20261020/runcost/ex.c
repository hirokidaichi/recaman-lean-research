// print TS instances (r=2) at last clock n-1 with slack(0,q*) == target, minimal (no shorter prefix removal) not enforced.
#include <stdio.h>
#include <stdlib.h>
int main(int c,char**v){int n=atoi(v[1]),tg=atoi(v[2]),R=atoi(v[3]); long shown=0;
 for(long m=0;m<(1L<<(n-1));m++){ int s[64],F[65],G[65],E[64],dd[65];
  if(!(m&1)) ; // allow
  for(int i=0;i<n-1;i++) s[i]=((m>>i)&1)?1:-1; s[n-1]=1; F[0]=G[0]=0; for(int i=0;i<n;i++){F[i+1]=F[i]+s[i];G[i+1]=G[i]+F[i+1];}
  #define W(t,b) (F[b]==F[t]+1&&G[b]-G[t]==((b)-(t))*F[t])
  for(int b=0;b<n;b++){E[b]=0; if(s[b]>0) for(int t=b-3;t>=0;t-=4) if(W(t,b)){E[b]=1;break;}}
  dd[0]=0; for(int u=0;u<n;u++) dd[u+1]=dd[u]+(s[u]<0)-(s[u]>0&&E[u]);
  int b=n-1,r=0,bs[8]; int qs=0;
  while(r<R){ if(b<0||!E[b]) break; bs[r++]=b; qs=b; while(qs>0&&s[qs-1]<0) qs--; b=qs-1; }
  if(r<R) continue; if(dd[qs]!=tg) continue;
  // require minimal: string starts at 0 needed? skip strings where dropping first clock keeps property: just print first few with s[0]=S
  if(s[0]>0) continue;
  printf("%s q*=%d d(q*)=%d |",( {static char buf[70]; for(int i=0;i<n;i++) buf[i]=s[i]>0?'A':'S'; buf[n]=0; buf;}),qs,dd[qs]);
  for(int k=R-1;k>=0;k--){ int bb=bs[k]; printf(" b=%d starts:",bb); for(int t=bb-3;t>=0;t-=4) if(W(t,bb)) printf(" %d(d=%d,a=%d,F=%d)",t,dd[t],0,F[t]); }
  printf("\n"); if(++shown>40) break; }
}
