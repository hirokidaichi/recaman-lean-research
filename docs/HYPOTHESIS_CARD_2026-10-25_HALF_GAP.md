# Hypothesis card: 任意の供給S-gapの半数上界

- ID: H-20261025-08
- Status: PROVED-LEAN
- Parent: R-20261025-01、E-381/E-385/E-389。fast全DAGと独立な一般r向けの量的不等式。
- Mode: 局所探索/活用。最初15分でold/local双方の新不等式を供給できなければ、範囲を隠さず停止。

## 一問・全量化子

任意padded BlockWord実prefix終端n、n<b、[b,b+j)が全S、元0からb+jが実EndNなら
2*j+2≤ones(seg f n (b−n))を導けるか。語長/深さ/A予算/free予算/jの上限なし。
旧E-389はj≤2*先行全A−2。新しい上界も先行の全Aを数え、free A個数と取り違えない。
受入にはlocal/old両方を覆う全EndNの不等式と、任意jで等号となる明示供給語族を含める。
等号の全word分類は別の問いであり、このunitの達成をその供給と誤記しない。

## 紙上chain

Q(w)=2 areaW(w)+mass(w)(mass(w)−1)はSをappendしても不変。
local供給gap jは、元wのsuffix vでmass(v)=j+1かつQ(v)=0の場合に限る。
全A数Aのarea最小値から、正mass RでQ=0なら2R≤A。従って2j+2≤A。
old側はR=1−A+N（Nはgapを含むtail総S）、旧prefix二次面積下界とgap前wordのcount下界から
N(N−2A+2)+2Aj≤0、従って2Aj≤(A−1)^2。old必要mass>=1とarea>=1でA>=2、整数性から2j+2≤A。
localとoldを混同せず、実S-runとのseg/EndN接続を最後に行う。

## 反証pass・費用

w空/A0/A1、j0、SAA、SSAAAA S、jを任意に増やす等号族S^(j+1) A^(2j+2) S^jを紙上攻撃。
old側に自由なtagを置いたモデルでは同じ入力が供給されないので、全EndNへの根拠にしない。
新CPU探索は当初0。まず既知area/count定理から紙上chainを確認し、Lean・Audit・G5と全体check成功時だけ昇格。
修理は数学1回まで。old側で失敗したらlocal結果を全EndNへ膨らませず別label/停止理由を保存する。
全DAGのCPUと親elapsedを二重加算しない。監査/引継ぎと7:45/8:00制限を残す。

## 判定

E-407。local/old必要signature/実EndNの全S-gap半数上界と全jの等号族を個別Leanで検証。最初の完成報告はBool.or分岐のコンパイル完了を先走ったため訂正し、half-gap-final-lean-2.logのexit0を確認した。数学的な修理/主張変更はない。新checkerのpruningはこの一般証明を使い、個別stateの仮定をkernelへ供給する。全体check/人間レビューは別。

最終全体check: final-check-2.log、412jobs/2811宣言成功。old/local/元0実語の条件と全Aの範囲を維持。次は10/26 free-gapカード。

## 当日journal確定実績
親cycle R-20261025-01: 06:01:21.862027〜07:59:10.380882、確認済み117分48.519秒、不足2分11.481秒。
このcardを別cycleとして加算せず、実unit/phaseの内訳は[当日DAILY](RESEARCH_HANDOFF_2026-10-25_DAILY.md)と[journal](data/daily_research/2026-10-25.json)を参照。待機・未確認・CPU・前日分の加算なし。
