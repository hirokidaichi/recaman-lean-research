// Local-shortening test. For each string x of length n (bit=1 means A) with exc(x)>=thr and Lam(x)>=lmin,
// search a replacement of a factor x[i,i+l) (4<=l<=wmax) by any string of length l-d (d=4 default) giving y with exc(y)>=exc(x).
// mode 0: any position; mode 1: interior only (i>0, i+l<n); mode 2: interior and factor inside the longest minimal window.
// Also option requireLam: Lam(y) < Lam(x).
#include <stdio.h>
#include <stdlib.h>
static int lam_g;
int exc(const signed char*s,int n,int*lam){ int F[80],G[80]; F[0]=0;G[0]=0;
  for(int i=0;i<n;i++){F[i+1]=F[i]+s[i];} for(int u=1;u<=n;u++)G[u]=G[u-1]+F[u];
  int e=0,S=0,L=0; for(int b=0;b<n;b++){ if(s[b]<0){S++;continue;}
    for(int t=b-3;t>=0;t-=4){ if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]){ e++; if(b-t>L)L=b-t; break;} } }
  if(lam)*lam=L; return e-S; }
int lwin_t,lwin_b;
void longest(const signed char*s,int n){ int F[80],G[80]; F[0]=0;G[0]=0;
  for(int i=0;i<n;i++){F[i+1]=F[i]+s[i];} for(int u=1;u<=n;u++)G[u]=G[u-1]+F[u];
  int L=0; for(int b=0;b<n;b++){ if(s[b]<0)continue;
    for(int t=b-3;t>=0;t-=4){ if(F[b]==F[t]+1 && G[b]-G[t]==(b-t)*F[t]){ if(b-t>L){L=b-t;lwin_t=t;lwin_b=b;} break;} } } }
int main(int argc,char**argv){ int n=atoi(argv[1]), thr=atoi(argv[2]), lmin=atoi(argv[3]), wmax=atoi(argv[4]), mode=atoi(argv[5]), reqlam=atoi(argv[6]); int d=argc>7?atoi(argv[7]):4;
  long tested=0,fail=0; signed char x[80],y[80];
  for(long m=0;m<(1L<<n);m++){ for(int i=0;i<n;i++) x[i]=((m>>i)&1)?1:-1;
    int lx; int ex=exc(x,n,&lx); if(ex<thr||lx<lmin) continue; tested++;
    if(mode==2) longest(x,n);
    int ok=0;
    for(int l=d; l<=wmax && !ok; l++) for(int i=0;i+l<=n && !ok;i++){
      if(mode>=1 && (i==0||i+l==n)) continue;
      if(mode==2 && !(i>=lwin_t && i+l<=lwin_b)) continue;
      int nl=l-d;
      for(long r=0;r<(1L<<nl) && !ok;r++){ int k=0; for(int a=0;a<i;a++)y[k++]=x[a]; for(int a=0;a<nl;a++)y[k++]=((r>>a)&1)?1:-1; for(int a=i+l;a<n;a++)y[k++]=x[a];
        int ly; int ey=exc(y,k,&ly); if(ey>=ex && (!reqlam || ly<lx)) ok=1; } }
    if(!ok){ fail++; if(fail<=8){ for(int i=0;i<n;i++)putchar(x[i]>0?'A':'S'); printf("  exc=%d Lam=%d\n",ex,lx);} } }
  printf("n=%d thr=%d lmin=%d wmax=%d mode=%d reqlam=%d d=%d: tested=%ld fail=%ld\n",n,thr,lmin,wmax,mode,reqlam,d,tested,fail); }
