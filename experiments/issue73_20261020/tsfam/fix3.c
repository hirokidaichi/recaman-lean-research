// greatest fixpoint for LOCALIZED pair invariant: bound on slack from the OLDER start t_o.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define DM 7
#define QM 20
#define NQ (2*QM+1)
#define NS ((2*DM+1)*NQ)
unsigned char phi[2][NS][NS], psi[2][NS];
static inline int inw(int D,int Q){return D>=-DM&&D<=DM&&Q>=-QM&&Q<=QM;}
static inline int id(int D,int Q){return (D+DM)*NQ+(Q+QM);}
static inline int MAX(int a,int b){return a>b?a:b;} static inline int MIN(int a,int b){return a<b?a:b;}
int psiany(int D,int Q){ if(!inw(D,Q)) return 0; int x=id(D,Q); int v=MIN(psi[0][x],psi[1][x]); if(D==0&&Q==0) v=0; return v; }
int phiany(int D1,int Q1,int D2,int Q2){ if(!inw(D1,Q1)) return 0; if(!inw(D2,Q2)) return psiany(D1,Q1);
  int x=id(D1,Q1),y=id(D2,Q2); int b=99; for(int c=0;c<2;c++){ int v=MAX(phi[c][x][y],psi[c][x]); b=MIN(b,v);} return b; }
void pr(int c,int D,int Q,int*Dp,int*Qp){ if(c){*Dp=D-1;*Qp=Q-2*D+1;} else {*Dp=D+1;*Qp=Q;} }
int J1(int c,int D,int Q){ int a,b; pr(c,D,Q,&a,&b);
  if(!c) return psiany(a,b)+1;
  int v=psiany(a,b); int e=MAX(psiany(a,b),phiany(a,b,1,0))-1; if(a==1&&b==0) e=MIN(e,psiany(a,b)-1); v=MIN(v,e); return MAX(v,0); }
int J2(int c,int D1,int Q1,int D2,int Q2){ int v=99;
  if(D2==0&&Q2==0) v=MIN(v,J1(c,D1,Q1));
  int a,b,e,f; pr(c,D1,Q1,&a,&b); pr(c,D2,Q2,&e,&f); int o;
  if(!c) o=phiany(a,b,e,f)+1;
  else { int P=phiany(a,b,e,f); int en=MAX(P,phiany(a,b,1,0))-1; if((a==1&&b==0)||(e==1&&f==0)) en=MIN(en,P-1); o=MIN(P,en); }
  v=MIN(v,o); if(v<0) v=0; if(!c&&v<1) v=1; return v; }
int main(int argc,char**argv){ FILE*fp=fopen(argv[1],"rb"); fread(phi,1,sizeof phi,fp); fread(psi,1,sizeof psi,fp); fclose(fp);
  for(int it=0;;it++){ long ch=0;
    for(int c=0;c<2;c++) for(int x=0;x<NS;x++){ int D=x/NQ-DM,Q=x%NQ-QM; int j=J1(c,D,Q); if(!c&&j<1)j=1; if(j<psi[c][x]){psi[c][x]=j;ch++;} }
    for(int c=0;c<2;c++) for(int x=0;x<NS;x++) for(int y=0;y<NS;y++){ int j=J2(c,x/NQ-DM,x%NQ-QM,y/NQ-DM,y%NQ-QM); if(j<phi[c][x][y]){phi[c][x][y]=j;ch++;} }
    fprintf(stderr,"iter %d changes %ld\n",it,ch); if(!ch) break; }
  for(int o=0;o<2;o++){ printf("TS' (c=A) older=%s: rows j cols i: bound on slack from older start\n",o?"t2":"t1");
   for(int j=0;j<6;j++){ for(int i=0;i<6;i++){ int D1=j+1,Q1=0,D2=i+j,Q2=-(2*i+1); if(!inw(D2,Q2)){printf("  -");continue;}
      int v=o?MAX(phi[1][id(D2,Q2)][id(D1,Q1)],psi[1][id(D2,Q2)]):MAX(phi[1][id(D1,Q1)][id(D2,Q2)],psi[1][id(D1,Q1)]); printf("%3d",v);} printf("\n"); } }
  FILE*out=fopen(argv[2],"wb"); fwrite(phi,1,sizeof phi,out); fwrite(psi,1,sizeof psi,out); fclose(out); return 0; }
