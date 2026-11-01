// greatest-fixpoint pair invariant: start from data table (min d), lower by one-step backward justification until inductive.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define DM 7
#define QM 20
#define NQ (2*QM+1)
#define NS ((2*DM+1)*NQ)
#define CAP 7
unsigned char f[2][NS][NS], g[2][NS];
static inline int inw(int D,int Q){return D>=-DM&&D<=DM&&Q>=-QM&&Q<=QM;}
static inline int id(int D,int Q){return (D+DM)*NQ+(Q+QM);}
static inline int MAX(int a,int b){return a>b?a:b;} static inline int MIN(int a,int b){return a<b?a:b;}
int ID00, ID10;
int gany(int D,int Q){ if(!inw(D,Q)) return 0; int x=id(D,Q); int v=MIN(g[0][x],g[1][x]); if(x==ID00) v=MIN(v,0); return v; }
int Fany(int D1,int Q1,int D2,int Q2){ int a=inw(D1,Q1),b=inw(D2,Q2);
  if(!a&&!b) return 0; if(!a) return gany(D2,Q2); if(!b) return gany(D1,Q1);
  int x=id(D1,Q1),y=id(D2,Q2); int best=0; for(int c=0;c<2;c++){ int v=MAX(f[c][x][y],MAX(g[c][x],g[c][y])); if(c==0||v<best) best=v; } return best; }
// predecessor of state (D,Q) under clock c (c=1 A, 0 S)
void pr(int c,int D,int Q,int*Dp,int*Qp){ if(c){*Dp=D-1;*Qp=Q-2*D+1;} else {*Dp=D+1;*Qp=Q;} }
int Jsingle_old(int c,int D,int Q){ int Dp,Qp; pr(c,D,Q,&Dp,&Qp); int v;
  if(!c) return gany(Dp,Qp)+1;
  v=gany(Dp,Qp); // nonendable
  int e=MAX(MAX(gany(Dp,Qp),gany(1,0)),Fany(Dp,Qp,1,0))-1; if(Dp==1&&Qp==0) e=MIN(e,gany(Dp,Qp)-1);
  v=MIN(v,e); return MAX(v,0); }
int Jpair(int c,int D1,int Q1,int D2,int Q2){ int v=99;
  if(D1==0&&Q1==0) v=MIN(v,Jsingle_old(c,D2,Q2));
  if(D2==0&&Q2==0) v=MIN(v,Jsingle_old(c,D1,Q1));
  int a,b,cc,dq; pr(c,D1,Q1,&a,&b); pr(c,D2,Q2,&cc,&dq);
  int o;
  if(!c) o=Fany(a,b,cc,dq)+1;
  else { int ne=Fany(a,b,cc,dq);
    int e=MAX(Fany(a,b,cc,dq),MAX(Fany(a,b,1,0),Fany(cc,dq,1,0)))-1;
    if((a==1&&b==0)||(cc==1&&dq==0)) e=MIN(e,Fany(a,b,cc,dq)-1);
    o=MIN(ne,e); }
  v=MIN(v,o); if(v<0) v=0; if(!c&&v<1) v=1; return v; }
int main(int argc,char**argv){ FILE*fp=fopen(argv[1],"rb"); fread(f,1,sizeof f,fp); fread(g,1,sizeof g,fp); fclose(fp);
  ID00=id(0,0); ID10=id(1,0);
  for(int it=0;;it++){ long ch=0;
    for(int c=0;c<2;c++) for(int x=0;x<NS;x++){ int D=x/NQ-DM,Q=x%NQ-QM;
      int j; if(D==0&&Q==0) j=c?0:1; else { j=Jsingle_old(c,D,Q); if(!c&&j<1) j=1; }
      if(j<g[c][x]){g[c][x]=j;ch++;} }
    for(int c=0;c<2;c++) for(int x=0;x<NS;x++) for(int y=x;y<NS;y++){ int D1=x/NQ-DM,Q1=x%NQ-QM,D2=y/NQ-DM,Q2=y%NQ-QM;
      int j=Jpair(c,D1,Q1,D2,Q2); if(j<f[c][x][y]){f[c][x][y]=f[c][y][x]=j;ch++;} }
    fprintf(stderr,"iter %d changes %ld\n",it,ch); if(!ch) break; }
  printf("TS' pairs (c=A) after fixpoint, rows j, cols i:\n");
  for(int j=0;j<6;j++){ for(int i=0;i<6;i++){ int D2=i+j,Q2=-(2*i+1); if(!inw(j+1,0)||!inw(D2,Q2)){printf("  -");continue;} printf("%3d",f[1][id(j+1,0)][id(D2,Q2)]); } printf("\n"); }
  FILE*o=fopen(argv[2],"wb"); fwrite(f,1,sizeof f,o); fwrite(g,1,sizeof g,o); fclose(o); return 0; }
