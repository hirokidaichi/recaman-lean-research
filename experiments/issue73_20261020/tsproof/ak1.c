// min area(t,q] and min D over starts t<k1, per slack s (prefix-H, last clock A)
#include <stdio.h>
#include <stdlib.h>
int n,s[64],F[65],G[65];
int endab(int b,int p){ if(s[b]<0) return 0; for(int t=b-3;t>=p;t-=4) if(F[b]==F[t]+1&&G[b]-G[t]==(b-t)*F[t]) return 1; return 0;}
int main(int c,char**v){n=atoi(v[1]); long mn[4]={999,999,999,999}; int mD[4]={99,99,99,99};
 for(long m=0;m<(1L<<(n-1));m++){ for(int i=0;i<n-1;i++) s[i]=((m>>i)&1)?1:-1; s[n-1]=1; F[0]=G[0]=0; for(int i=0;i<n;i++){F[i+1]=F[i]+s[i];G[i+1]=G[i]+F[i+1];}
  int d=0,ok=1,k1=0; for(int b=0;b<n;b++){ if(s[b]<0)d++; else if(endab(b,0)) d--; if(d<0){ok=0;break;} if(d==0) k1=b+1;} if(!ok||d>3) continue;
  for(int t=0;t<k1;t++){ int D=F[n]-F[t]; long Ar=G[n]-G[t]-(long)(n-t)*F[t]; if(D<mD[d]) mD[d]=D; if(Ar<mn[d]){mn[d]=Ar; for(int k=0;k<n;k++){if(k==k1)putchar('|');putchar(s[k]>0?'A':'S');} printf(" s=%d t=%d D=%d area=%ld\n",d,t,D,Ar);} }
 }
 for(int a=0;a<4;a++) printf("s=%d minArea=%ld minD=%d\n",a,mn[a],mD[a]);}
