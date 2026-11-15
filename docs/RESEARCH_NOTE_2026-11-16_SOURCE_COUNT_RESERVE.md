# 実供給の件数だけでは初期S源の深さを払えない

2026-11-16、H-20261116-02 / R-20261116-01。結論は全hの紙上構成（PROVED-PAPER、未Lean・人間レビュー未）。反証されるのは「exclusive old供給の件数Dだけの有限関数で、全元供給を保つ残存initial-S headを選べる」という無条件輸送機構。V<=全元free、一般C1、標準軌道の反例ではない。

任意h>=2で元有限語

    w_h = S^h A^(2h) S^(h-1) A

を取り、長さ4h、cutoff h、future K=3hとする。fはw_hを読む元符号列で範囲外はA（証明に使う正不足/計数は4hまで）。H(k)=Fw f k、B(k)=Σ_{i=1}^k H(i)。元Winの定義は0<q-t、H(q)=H(t)+1、B(q)-B(t)-(q-t)H(t)=0。

## 全元actual供給を尽くす

initial-S内と後続S内にはAがない。第一A-rayのclock q=h+i（0<=i<2h）について、source t>=hなら窓はAのみであり、rise1なら長さ1/area1となってWinでない。t<hの全旧sourceはinitial-S quadraticにより

    2<=i<=h+1,  i(i+1)=3i(i-1)

を満たす必要十分条件を持つ。右式は2i(i-2)=0であるからi=2のみ。その唯一のsourceはh-1。h>=2なのでこのclockはray内にあり、元EndN f0(h+2)、非EndN f h(h+2)を得る。

最後のAのclockはq*=4h-1、H(q*)=1、B(q*)=0。実際、最初hSの面積は-h(h+1)/2、2hAの面積はh、h-1個のSの面積はh(h-1)/2で、合計0。sourceは高さ0でなければならない。q*より前の全高さ0時計は0と2hだけ：initial-Sは0のみ、上昇A-rayは2hのみ、最後のS-rayは高さhから1までで0へ戻らない。B(0)=0、B(2h)=-h^2。source0はarea0、source2hはarea h^2>0であるから、全元sourceは0だけ。従ってq*もexclusive old actualである。

以上より、元actual Aは正確にh+2と4h-1の2件。どちらもexclusive old、他の全Aは元freeで、全A数2h+1、free=2h-1。old以外の源を捨てた計数でなく、全源を排除した結果である。

## 正不足・reserve・端点

全非空prefixの元正不足 E0+1<=S0 は内部に成立する。initial-S内はE0=0、第一A-ray以後の最後A前はE0<=1/S0>=h>=2、最後A後はE0=2/S0=2h-1>=3。
E712のtail reserve U=max_{1<=k<=K}(E(k)+1-S(k))_+ は2。第三Aの直後、まだtail S0の時にE1なので2を達成し、それ以外は2を越えない。exclusive source深さの最大Vはh（最後source0）、第一rayのsource深さは1。従ってD=2、U=2、V=h、最小供給・positive保存head C*=h。
E712でVに含むq=Kはここではclock4hである。この時計の高さは2なので必要source高さ1はinitial-Sにない。仮にlocal supplyがあってもexclusive oldではない。D/Vへ未計上の端点sourceを混入しない。K=3hは最後actual q*=4h-1を計数内に含む。

## 件数だけの任意の有限head規則を反証

任意g:Nat->Natを取り、h>max(2,g(2))を選ぶ。D=2だがC=g(D)<hであり、cut後のsource下限h-Cは0より大きい。最後targetは唯一source0を失い、元actual同値が壊れる。g(2)がどれほど大きくてもこのhを選べるので、単一係数だけでなくDだけの全有限関数を排除する。

より正確には、0<=C<=hについて失う実供給件数はC=hなら0、C=0なら2、1<=C<hなら1。C>=1では第一rayのsource h-1を残し、最後source0を失う。元futureのfreeはその件数だけ増える（E713の式に一致）。2<=C<hではcut後も実正不足が成立する：head C>=2、第一rayの保持供給1、最後targetはfreeであり、その後もE<=1/S>=C。C=0/1では第三A直後にpositiveが壊れる。h2/C2はcutなしで失う供給0という境界を保持する。

この族はD<=free（2<=2h-1）もV<=free（h<=2h-1）も満たす。最終S-gap j=h-1に対しfree=2h-1>=j+1で、C1反例ではない。C1反例という追加条件の下だけで成立する特殊操作を反証したとも言わない。ここで排除するのは元positive-history全域で件数Dだけに基づき実供給を保つ操作である。

## 入力と新規性・有限検算

三runのsharp Win S^h A^(2h) S^(h-1)自体は既存E408の入力で、新しいWinや固定深さcoverageと数えない。新しい一般機構no-goは、全sourceを分類してD=2を全hで固定し、源生存費用V=hが非有界、全件数関数gによる保存不能を導いた点にある。
本日のguardを確認したcooperative/no-child single-Pythonで、事前凍結したh2..24をreverse literal全source、h25..64をforward key全sourceの二方式で検算。各hの全Cとpositive/free/source式を確認。これはCOMPUTEDの有限支持であり、全hの根拠は上の時計分類と閉じた式。固定族の異なるhであり、統計的なfresh holdoutとは呼ばない。argv/source hash/revision/CPU終了receiptはdocs/data/depth_general_20261116/COUNT_RESERVE_PROTOCOL.json及びH02-count-*を参照。

## 残る一問

H-20261116-02のV<=全元freeはCONJECTURED。source-depth finite probeは凍結範囲で反例なし、方法STOPPED、範囲拡張しない。選んだold-source endpointでのtail供給債務T(k)=E(k)-S(k)を元actualから抑える新辺が必要。d=F(k)+T(k)-1の恒等式を新定理へ数えない。件数だけのhead規則は停止し、元source深さ又は有償のarea/deficit reserveを保持する。

## 別passでのconsumer/domain監査（06:36以降）

- 元padded境界はn=0/空BlockWordで成立し、initial-S headはsourceを含む元0から読む。cut後のprefixを新しいBlockWordと再仮定しない。符号は同じfutureをコピーする操作で、E713の保持source cutoff h-Cの会計を使う。
- 末尾targetの直前S-gapはh-1で、cutの対象は先頭Sだけ。2<=C<hなら末尾gap自体は不変でも、targetの唯一源0が消えるのでactual targetを保持できない。free保存だけでなくtarget保存の義務も壊れる。
- F=2h-1で最終free-gapの余裕F-(j+1)=h-1が正。従って「元C1 counterである」を追加した限定版をこの族で停止しない。有限positive historyの全域での輸送を狙う案のno-goと、counter域の未知命題を区別する。
- この族ではVが最大でUは一定、E715ではV=1のままDが非有界。二つを合わせてDとVを同じ費用と扱わない。両族ともfreeが増えるため、V<=freeやD<=freeの成否は別。
- q*=4h-1を数えず終端4hだけを対象にした弱いadapterでは反証を失う。元statementの全q<=K、prefix実供給/free、最終Aを同じ時刻で監査する。
- 既存E408の二run sharp窓、E712最小性、E713 source-loss式を再証明しただけとは数えない。新しい辺は全hでDを固定した全actual分類と「任意有限g(D)」に対する源生存の障害である。
