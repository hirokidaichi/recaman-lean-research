# H-20261031-02: 二caseの全三run head local certificate

Status CONJECTURED、R-20261031-01の活用子unit、H01の残り枠から支出。単独の新研究60分を加算しない。

全h,M,m,L,s,U>=1、h+m+s=M+L+U=10、head Sh AM Sm AL Ss AU。B46ならSv1後のA5、B56ならSv2後のA7。area=-Bで各rayのlocal供給数<=2を問う。全old排除・実counter二caseはH01個別Leanから供給する。自由Endable tagやfree結論を入力しない。

有限反証: discovery M<=L 720heads、独立holdout M>L576heads、B46は25head/B56は36head、違反0、local供給最大2、非供給最小3/5。これはCOMPUTEDだけで、全old/actual命題ではない。全clock0/2だけという強化は未宣言・未採用で、最大数と特定clockを混同しない。

依存chain: 正整数3compositionの構造的包含証明→36×36 head候補→同じareaで61headに数学的pruning→61個のlocal count certificate→任意頭部local<=2→E441/E465の全old排除→同じactual EndN count→lastfree>=3/5→headfree4と区間加法→fullfree>=R。最弱未知edgeは61head local certificateと構造的包含のkernel検証。

最初の検証は10CPU per-process/20wall/Lean -M512。gate候補cell=1296頭部包含候補+61 local-count行=1357、<=3000。これは実行費用の保証ではない。source suffix展開の内部reductionは追加演算であり1357CPU単位とは呼ばない。必要な出力と実資源を測定し、未検証部分を昇格しない。kernel失敗は資源追加/compiled移動だけで再開せず、独立した数学的pruning/因数化を一回まで必要とする。旧H06/r4表の再開ではない。

数学CPUはH01 preflightの2秒のうち0.071416秒を使用、追加数学worker実行なし。certificate validationはLean検証CPUとして別記し、08時前deadlineを守る。既存全oldprefix/histories/一般四runへ有限局所範囲を外挿しない。

## 判定 06:11

同じmonolithic certificate layoutは512MB kernel memory/heartbeatでSTOPPED。61行の全包含/actual countは未検証でありPROVEDへ上げない。sourceはpacket .lean.txtへ隔離。次は独立したsource平方非平方/firstA因数化という数学的pruningを導入する。一回修理はこの解析的機構に限り、同jobへの時間/メモリ追加やcompiled移動だけでは再開しない。

## 数学的pruningへの切替（同じjobの資源追加ではない）

同じheadから最初d個Sを除くと供給keyは `(d-(10+v))^2=101+20v-B`。二caseでは75/85となり非平方なので初期S源は全clock不可能。最後rayのlocal<=5はこの源排除と定符号run予算だけで供給できる。case2はA7なので必要free2を既に支払える。

case1のfirstA源がclock<5に存在するとh=6/i=1。moment式M(m+s)+Ls=27とmass/countからM6/Ls3、s1又は3になる。同時にsecondA源があればそのkey式は4の倍数=6/30となり不可能。したがって「firstA又はsecondAの一方だけ」が課金対象となりlocal<=4、A5のfree1を得る。全表local<=2という計算より弱いが、最初に固定した必要free1/2と同じ結論へ十分であり、未証明local<=2を仮定しない。

## 最終判定（数学機構は通過、table方法だけSTOPPED）

E468/E469 PROVED-LEAN。初期S source排除、firstA/secondA不両立、local4/5から必要actual free1/2と元p free-gapを完了。強いlocal<=2と61-row tableは未Leanのまま。計算とkernelを区別し、停止methodを証明したことにしていない。

## 日次の保存判断（保存時の監査）
強い無制限補助命題はCONJECTUREDのまま。有限計算はCOMPUTEDだけで、独立全長source/count証明へ昇格していない。停止方法を再実行しない。
親cycleはR-20261031-01のみ。実時計/commands/CPU/変更sourceの正本は当日DAILY、journal、`data/ten_head_20261031/SOURCE_VALIDATION_INDEX.json`と`CPU_SUMMARY.json`。元0/pと全old prefixを維持。
当card IDで確認された閉区間 2 件、合計 564.860 秒（他unit/親cycleへ二重加算しない）。個別start/end/unit/phaseはjournalの同IDを参照。open区間を含めない。
