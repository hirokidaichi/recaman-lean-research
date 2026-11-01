// slack-SM nodes (last A, prefix-H): min g on [k1,q], straddlers (endable c in [k1,q) with all windows starting <k1)
#include <stdio.h>
#include <stdlib.h>
int N,SM,s[128],F[129],G[129],E[128],dd[129],ES[128]; int mng[8]; int nstr[8];
int endab(int b,int lo){ if(s[b]<0) return 0; for(int t=b-3;t>=lo;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
void node(int n){ int d=dd[n]; if(s[n-1]<0||d>SM) return; int k1=0; for(int k=0;k<=n;k++) if(dd[k]==0) k1=k;
  int mg=0; for(int k=k1;k<=n;k++) if(F[k]-F[k1]<mg) mg=F[k]-F[k1];
  if(mg<mng[d]){ mng[d]=mg; printf("newmin s=%d g=%d x=",d,mg); for(int k=0;k<n;k++){if(k==k1)putchar('|');putchar(s[k]<0?'S':(E[k]?'a':'A'));} printf("\n"); }
  for(int c=k1;c<n;c++) if(E[c] && !endab(c,k1)){ if(nstr[d]++<6){ printf("straddle s=%d c-k1=%d x=",d,c-k1); for(int k=0;k<n;k++){if(k==k1)putchar('|');putchar(s[k]<0?'S':(E[k]?'a':'A'));} printf("\n");} break; } }
void dfs(int n){ if(n>0) node(n); if(n==N) return;
  for(int v=-1;v<=1;v+=2){ s[n]=v; F[n+1]=F[n]+v; G[n+1]=G[n]+F[n+1]; E[n]=endab(n,0);
    int d=dd[n]+(v<0?1:0)-(E[n]?1:0); if(d<0) continue; dd[n+1]=d; dfs(n+1); } }
int main(int c,char**v){N=atoi(v[1]); SM=atoi(v[2]); dfs(0); for(int a=0;a<=SM;a++) printf("s=%d ming=%d nstraddle=%d\n",a,mng[a],nstr[a]); return 0;}
