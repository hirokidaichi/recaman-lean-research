// greatest fixpoint, key (c, r, xo, xn). Sound one-step backward justification (see report).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define DM 7
#define QM 20
#define NQ (2*QM+1)
#define NS ((2*DM+1)*NQ)
#define R 8
#define INF 99
unsigned char phi[2][R+1][NS][NS], psi[2][R+1][NS];
static inline int inw(int D,int Q){return D>=-DM&&D<=DM&&Q>=-QM&&Q<=QM;}
static inline int id(int D,int Q){return (D+DM)*NQ+(Q+QM);}
static inline int MAX(int a,int b){return a>b?a:b;} static inline int MIN(int a,int b){return a<b?a:b;}
// lower bound for slack(0,m) given start0 state (D,Q) at m and r at m (any last clock); base m=0 included.
int psiany(int r,int D,int Q){ if(!inw(D,Q)) return MAX(0,-D); int x=id(D,Q); int v=MIN(psi[0][r][x],psi[1][r][x]); if(D==0&&Q==0&&r==0) v=0; return v; }
int phiany(int r,int D1,int Q1,int D2,int Q2){ if(!inw(D1,Q1)) return MAX(0,-D1); if(!inw(D2,Q2)) return psiany(r,D1,Q1);
  int x=id(D1,Q1),y=id(D2,Q2); int b=INF; for(int c=0;c<2;c++){ int v=MAX(phi[c][r][x][y],psi[c][r][x]); b=MIN(b,v);} return b; }
void pr(int c,int D,int Q,int*Dp,int*Qp){ if(c){*Dp=D-1;*Qp=Q-2*D+1;} else {*Dp=D+1;*Qp=Q;} }
// generic: older pred (a,b); newer pred (e,f) or none (hasN=0).
int val(int hasN,int a,int b,int e,int f,int r){ return hasN? phiany(r,a,b,e,f) : psiany(r,a,b); }
int J(int c,int r,int hasN,int D1,int Q1,int D2,int Q2){
  int a,b,e=0,f=0; pr(c,D1,Q1,&a,&b); if(hasN) pr(c,D2,Q2,&e,&f);
  int v=INF;
  if(!c){ // S step: r unchanged, slack +1
    v=val(hasN,a,b,e,f,r)+1;
  } else if(r==0){ // non-endable A: no pred state may be (1,0)
    if(a==1&&b==0) return INF; if(hasN&&e==1&&f==0) return INF;
    for(int rp=0;rp<=R;rp++) v=MIN(v,val(hasN,a,b,e,f,rp));
  } else { // endable A
    int rlo=r-1, rhi=(r==R)?R:r-1;
    for(int rp=rlo;rp<=rhi;rp++){ int P=val(hasN,a,b,e,f,rp);
      int w=MAX(P,phiany(rp,a,b,1,0))-1; // witness: a newer start with (1,0)
      if(a==1&&b==0) w=MIN(w,P-1); if(hasN&&e==1&&f==0) w=MIN(w,P-1);
      v=MIN(v,w); }
  }
  if(v<-D1) v=-D1; if(v<0) v=0; if(!c&&v<1) v=1; return v; }
int J2(int c,int r,int D1,int Q1,int D2,int Q2){ int v=J(c,r,1,D1,Q1,D2,Q2); if(D2==0&&Q2==0) v=MIN(v,J(c,r,0,D1,Q1,0,0)); return v; }
void trace(int c,int r,int D1,int Q1,int D2,int Q2,int depth){
  for(int k=0;k<depth;k++){ int v=phi[c][r][id(D1,Q1)][id(D2,Q2)];
    printf("  step -%d: c=%c r=%d old=(%d,%d) new=(%d,%d) V=%d\n",k,c?'A':'S',r,D1,Q1,D2,Q2,v);
    if(D2==0&&Q2==0){ if(J(c,r,0,D1,Q1,0,0)<=v){ printf("   -> fresh newer start; single-start chain\n"); return; } }
    int a,b,e,f; pr(c,D1,Q1,&a,&b); pr(c,D2,Q2,&e,&f); if(!inw(a,b)||!inw(e,f)){printf("   -> leaves window (%d,%d)/(%d,%d)\n",a,b,e,f);return;}
    // find pred achieving
    int best=INF,bc=0,br=0,bx=0; // bx: 0 = (e,f), 1 = witness (1,0)
    int rlo,rhi; if(!c){rlo=rhi=r;} else if(r==0){rlo=0;rhi=R;} else {rlo=r-1;rhi=(r==R)?R:r-1;}
    for(int rp=rlo;rp<=rhi;rp++) for(int cp=0;cp<2;cp++){
      int P=MAX(phi[cp][rp][id(a,b)][id(e,f)],psi[cp][rp][id(a,b)]);
      int W=MAX(phi[cp][rp][id(a,b)][id(1,0)],psi[cp][rp][id(a,b)]);
      if(!c){ if(P+1<best){best=P+1;bc=cp;br=rp;bx=0;} }
      else if(r==0){ if(P<best){best=P;bc=cp;br=rp;bx=0;} }
      else { if(P-1<best && P>=W){best=P-1;bc=cp;br=rp;bx=0;} if(W-1<best && W>=P){best=W-1;bc=cp;br=rp;bx=1;} } }
    printf("   pred c=%c r=%d via %s\n",bc?'A':'S',br,bx?"WITNESS (1,0) (third start)":"tracked pair");
    c=bc; r=br; D1=a; Q1=b; if(bx){D2=1;Q2=0;} else {D2=e;Q2=f;} } }
int main(int argc,char**argv){ FILE*fp=fopen(argv[1],"rb"); fread(phi,1,sizeof phi,fp); fread(psi,1,sizeof psi,fp); fclose(fp);
  for(int it=0;;it++){ long ch=0;
    for(int c=0;c<2;c++) for(int r=0;r<=R;r++) for(int x=0;x<NS;x++){ int j=J(c,r,0,x/NQ-DM,x%NQ-QM,0,0); if(j<psi[c][r][x]){psi[c][r][x]=j;ch++;} }
    for(int c=0;c<2;c++) for(int r=0;r<=R;r++) for(int x=0;x<NS;x++) for(int y=0;y<NS;y++){ int j=J2(c,r,x/NQ-DM,x%NQ-QM,y/NQ-DM,y%NQ-QM); if(j<phi[c][r][x][y]){phi[c][r][x][y]=j;ch++;} }
    fprintf(stderr,"iter %d changes %ld\n",it,ch); if(!ch) break; }
  int worst=INF,wj=0,wi=0,wr=0,wo=0;
  for(int o=0;o<2;o++){ printf("TS' (c=A) older=%s: rows j cols i: min over r of bound on slack from older start\n",o?"t2":"t1");
   for(int j=0;j<6;j++){ for(int i=0;i<6;i++){ int D1=j+1,Q1=0,D2=i+j,Q2=-(2*i+1); if(!inw(D2,Q2)){printf("  -");continue;}
      int m=INF; for(int r=0;r<=R;r++){ int v=o?MAX(phi[1][r][id(D2,Q2)][id(D1,Q1)],psi[1][r][id(D2,Q2)]):MAX(phi[1][r][id(D1,Q1)][id(D2,Q2)],psi[1][r][id(D1,Q1)]);
        if(v<m)m=v; if(v<worst){worst=v;wj=j;wi=i;wr=r;wo=o;} } printf("%3d",m);} printf("\n"); } }
  printf("worst %d at o=%d j=%d i=%d r=%d; trace:\n",worst,wo,wj,wi,wr);
  if(wo==0) trace(1,wr,wj+1,0,wi+wj,-(2*wi+1),40); else trace(1,wr,wi+wj,-(2*wi+1),wj+1,0,40);
  if(argc>2){FILE*out=fopen(argv[2],"wb"); fwrite(phi,1,sizeof phi,out); fwrite(psi,1,sizeof psi,out); fclose(out);} return 0; }
