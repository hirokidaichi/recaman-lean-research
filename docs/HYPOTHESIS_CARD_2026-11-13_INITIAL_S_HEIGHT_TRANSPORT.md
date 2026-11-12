# H-20261113-07: 高さで初期S源を排除し元actual/freeを運ぶ

- Status PROVED-LEAN (E709 restricted actual/free transport); continuation of independent depth-operation mechanism H06
- All source-sensitive depth-operation time H06+H07 is kept separate from first height/overlap block
- H06 no-go completed; unused unit time moves here rather than waiting for nominal duration

## Exact bounded question
任意元f:Nat→Bool、h,q,K:Nat。全i<hでf i=S。g(i)=f(h+i)。
(1) Fw f(h+q)<=Fw f h+1なら EndN f 0(h+q) ↔ EndN g 0 q を**全旧sourceから内部供給**できるか。
(2) 全h<=i<h+KのA始点でFw f i<=Fw f h+1なら、元全prefix free f 0(h+K)=free g 0 K と元EndN数の一致、元S数=h+strip S数、従って元不足=strip不足+hを得られるか。
全depth/run/区間長/A予算は無制限。元prefix全Sという条件は明記し、一般padded old historyへ勝手に拡張しない。新EndN/free同値を仮定するPropを作らない。

## Falsifier / acceptance / limits
h0/q0/ceiling1境界を紙上攻撃。ceiling2なら旧SAAA→stripAAA、target3→2でEndNが変わるかをkernel検査。全S prefixのsource高さだけを使い、未知oldsourceを切らない。既存SeparatorTailFreeGap.endN_nat_shiftはsource>=hの時計shiftだけであり、元source0→hの排除を今回内部証明する。
既存InitialSeparatorTrimは全A予算Bと残すS>=2B-1が必要。今回のtarget-height条件は全A予算も残すSも要求しない別pruningであり、その停止jobを再開しない。
free保存だけをC1 induction完成にしない。不足はh減るので、strip後の正不足を保持するには追加marginが必要。元actual/free保存のedgeとC1 domain保存を別々に判定する。

## Stop / cost
最初15分で新actual source edge/反例がなければ同機構を延長しない。research上限07:37、07:45新探索禁止。Lean各独立certificate -j1/-M512/10CPU/20wall、一修理。CPU数学探索追加0。
H06+H07という独立source-aware depth-operation blockに少なくとも25分を確保し、個々のカードの早期完了を待機で埋めない。局所未使用約22分を含む再配分として保存する。
