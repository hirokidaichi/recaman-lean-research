// greatest fixpoint, key (c, r, xo, x1, x2): xo = start 0, x1,x2 = states of (not nec. distinct) newer starts in (0,n].
// T = lower bound on slack(0,n). Init = top (99). Floors: 0 (H), -D(xo), >=1 after S.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifndef DM
#define DM 4
#endif
#ifndef QM
#define QM 9
#endif
#define NQ (2*QM+1)
#define NS ((2*DM+1)*NQ)
#ifndef R
#define R 4
#endif
#define INF 99
static unsigned char T[2][R+1][NS][NS][NS];
static inline int inw(int D,int Q){return D>=-DM&&D<=DM&&Q>=-QM&&Q<=QM;}
static inline int id(int D,int Q){return (D+DM)*NQ+(Q+QM);}
static inline int MAX(int a,int b){return a>b?a:b;} static inline int MIN(int a,int b){return a<b?a:b;}
static int Z;
// lookup at time m (>=0) : older (a,b), newer list e1,e2 (valid flags). If a newer is invalid/out of window, replace by (0,0) (fresh start m exists if m>=1).
int L(int r,int a,int b,int v1,int e1,int f1,int v2,int e2,int f2){
  if(!inw(a,b)) return MAX(0,-a);
  if(v1&&!inw(e1,f1)) v1=0; if(v2&&!inw(e2,f2)) v2=0;
  int y1=v1?id(e1,f1):Z, y2=v2?id(e2,f2):Z; int x=id(a,b);
  int v=MIN(T[0][r][x][y1][y2],T[1][r][x][y1][y2]);
  if(!v1&&!v2&&a==0&&b==0&&r==0) v=0; // base m=0
  return v; }
void pr(int c,int D,int Q,int*Dp,int*Qp){ if(c){*Dp=D-1;*Qp=Q-2*D+1;} else {*Dp=D+1;*Qp=Q;} }
int Jv(int c,int r,int D0,int Q0,int v1,int D1,int Q1,int v2,int D2,int Q2){
  int a,b,e1=0,f1=0,e2=0,f2=0; pr(c,D0,Q0,&a,&b); if(v1) pr(c,D1,Q1,&e1,&f1); if(v2) pr(c,D2,Q2,&e2,&f2);
  int v=INF;
  if(!c) v=L(r,a,b,v1,e1,f1,v2,e2,f2)+1;
  else if(r==0){ if(a==1&&b==0) return INF; if(v1&&e1==1&&f1==0) return INF; if(v2&&e2==1&&f2==0) return INF;
    for(int rp=0;rp<=R;rp++) v=MIN(v,L(rp,a,b,v1,e1,f1,v2,e2,f2)); }
  else { int rhi=(r==R)?R:r-1;
    for(int rp=r-1;rp<=rhi;rp++){ int P=L(rp,a,b,v1,e1,f1,v2,e2,f2);
      int w=MAX(P,MAX(L(rp,a,b,v1,e1,f1,1,1,0),L(rp,a,b,v2,e2,f2,1,1,0)))-1;
      if((a==1&&b==0)||(v1&&e1==1&&f1==0)||(v2&&e2==1&&f2==0)) w=MIN(w,P-1);
      v=MIN(v,w);} }
  if(v<-D0) v=-D0; if(v<0) v=0; if(!c&&v<1) v=1; return v; }
int J(int c,int r,int D0,int Q0,int D1,int Q1,int D2,int Q2){
  int f1=(D1==0&&Q1==0), f2=(D2==0&&Q2==0);
  int v=Jv(c,r,D0,Q0,1,D1,Q1,1,D2,Q2);
  if(f1) v=MIN(v,Jv(c,r,D0,Q0,0,0,0,1,D2,Q2));
  if(f2) v=MIN(v,Jv(c,r,D0,Q0,1,D1,Q1,0,0,0));
  if(f1&&f2) v=MIN(v,Jv(c,r,D0,Q0,0,0,0,0,0,0));
  return v; }
int main(int argc,char**argv){ Z=id(0,0); memset(T,INF,sizeof T);
  for(int it=0;;it++){ long ch=0;
    for(int c=0;c<2;c++) for(int r=0;r<=R;r++) for(int x=0;x<NS;x++) for(int y=0;y<NS;y++) for(int z=y;z<NS;z++){
      int j=J(c,r,x/NQ-DM,x%NQ-QM,y/NQ-DM,y%NQ-QM,z/NQ-DM,z%NQ-QM);
      if(j<T[c][r][x][y][z]){T[c][r][x][y][z]=j;T[c][r][x][z][y]=j;ch++;} }
    fprintf(stderr,"iter %d changes %ld\n",it,ch); if(!ch) break; }
  // TS' readout: older start = t1 (j+1,0) or t2; third slot free = min over all (take (0,0) = weakest since always present).
  for(int o=0;o<2;o++){ printf("TS' older=%s (min over r)\n",o?"t2":"t1");
    for(int j=0;j<5;j++){ for(int i=0;i<5;i++){ int A1=j+1,B1=0,A2=i+j,B2=-(2*i+1);
      if(!inw(A1,B1)||!inw(A2,B2)){printf("  -");continue;} int m=INF;
      for(int r=0;r<=R;r++){ int v= o? T[1][r][id(A2,B2)][id(A1,B1)][Z] : T[1][r][id(A1,B1)][id(A2,B2)][Z]; m=MIN(m,v);} printf("%3d",m);} printf("\n"); } }
  if(argc>1){FILE*f=fopen(argv[1],"wb"); fwrite(T,1,sizeof T,f); fclose(f);} return 0; }
