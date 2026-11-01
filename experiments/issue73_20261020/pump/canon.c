// canonical deletion rules: mode 3 = leftmost 4-factor with max #S; 4 = any max-#S factor; 5 = rightmost max-#S
#include <stdio.h>
#include <stdlib.h>
int exc(const signed char*s,int n){ int F[80],G[80]; F[0]=0;G[0]=0;
  for(int i=0;i<n;i++){F[i+1]=F[i]+s[i];} for(int u=1;u<=n;u++)G[u]=G[u-1]+F[u];
  int e=0,S=0; for(int b=0;b<n;b++){ if(s[b]<0){S++;continue;}
    for(int t=b-3;t>=0;t-=4){ if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]){ e++; break;} } }
  return e-S; }
int main(int argc,char**argv){ int n=atoi(argv[1]),thr=atoi(argv[2]),mode=atoi(argv[3]); long cnt=0,fail=0; signed char x[80],y[80];
  for(long m=0;m<(1L<<n);m++){ for(int i=0;i<n;i++) x[i]=((m>>i)&1)?1:-1; int ex=exc(x,n); if(ex<thr) continue; cnt++;
    int c[80],mx=-1; for(int i=0;i+4<=n;i++){ c[i]=(x[i]<0)+(x[i+1]<0)+(x[i+2]<0)+(x[i+3]<0); if(c[i]>mx)mx=c[i]; }
    int ok=0, first=1;
    int lo=0,hi=n-4,step=1; if(mode==5){lo=n-4;hi=0;step=-1;}
    for(int i=lo; (step>0? i<=hi : i>=hi) && !ok; i+=step){ if(c[i]!=mx) continue; if(mode!=4 && !first) break; first=0;
      int k=0; for(int a=0;a<n;a++) if(a<i||a>=i+4) y[k++]=x[a]; if(exc(y,k)>=ex) ok=1; }
    if(!ok){ fail++; if(fail<=5){ for(int i=0;i<n;i++)putchar(x[i]>0?'A':'S'); printf(" exc=%d\n",ex);} } }
  printf("n=%d thr=%d mode=%d strings=%ld fail=%ld\n",n,thr,mode,cnt,fail); }
