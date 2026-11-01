#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){int N=atoi(argv[1]);long eqc=0,bad=0,hv=0;
 for(int n=1;n<=N;n++) for(long m=0;m<(1L<<n);m++){
  int s[64],F[65];F[0]=0;for(int i=0;i<n;i++){s[i]=((m>>i)&1)?1:-1;F[i+1]=F[i]+s[i];}
  int nw[64];int e=0,nS=0;
  for(int b=0;b<n;b++){nw[b]=0;if(s[b]<0){nS++;continue;}
   for(int t=b-3;t>=0;t-=4){ if(F[b]!=F[t]+1) continue; long a=0; for(int u=t+1;u<=b;u++) a+=F[u]-F[t]; if(a==0) nw[b]++; }
   if(nw[b]) e++;}
  if(e>nS){hv++; if(hv<5){printf("H VIOL n=%d m=%ld\n",n,m);}}
  if(e==nS && n>0 && nw[n-1]){ eqc++;
   /* parse */ int exp[64]={0}; int i=0,ok=1;
   while(i<n){ if(s[i]>0){i++;continue;}
     if(i+3<n && s[i+1]>0&&s[i+2]>0&&s[i+3]>0){exp[i+3]=1;i+=4;continue;}
     int T[10]={-1,-1,1,1,1,1,-1,1,1,1}; int okt=(i+9<n); for(int j=0;j<10&&okt;j++) if(s[i+j]!=T[j]) okt=0;
     if(okt){exp[i+4]=1;exp[i+7]=1;exp[i+9]=1;i+=10;continue;}
     ok=0;break;}
   if(ok) for(int b=0;b<n;b++){ if((nw[b]>0)!=exp[b]) ok=0; if(nw[b]>1) ok=0; }
   if(!ok){bad++; if(bad<5){printf("EQ FAIL n=%d: ",n);for(int j=0;j<n;j++)putchar(s[j]>0?'A':'S');puts("");}}
  }}
 printf("N=%d Hviol=%ld eqcases=%ld eqbad=%ld\n",N,hv,eqc,bad);}
