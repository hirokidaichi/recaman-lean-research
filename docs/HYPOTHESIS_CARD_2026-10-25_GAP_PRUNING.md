# Hypothesis card: 証明したgap上界と予算判定を先に使うDAG checker

- ID: H-20261025-09
- Status: PROVED-LEAN（一般checker同値）。全r4分類E-404はCONJECTURED、single-file方法はSTOPPED
- Parent: R-20261025-01、H08の新しい2j+2<=A、H04/H07の同じr4分類kernel。

## 一問と保存する対象

任意state sでones(s.word)<=s.additions<=10なら、供給tag trueのmacroは2j+2>s.additionsでnoneか。
飽和trimではE390の全local保存を使い、非飽和では新しいwordSupply半数gap上界を使う。
false tagはfree予算、両tagは正不足balanceを先に判定し、拒否時にlocal scanを走らせない。
このprunedSuccessorsが元の全40候補successorsと等しいことをLeanで証明してから具体DAGで使う。
stateのword/A条件は各具体行でkernelに供給し、A11を遷移定義から切らない。

## 反証・受入・停止

empty/既知19番目が必要なword/飽和長gap/free A/A11を保持し、任意stateで旧定義との等式を確認。
2j+2<=Aは全Aに対する上界で、free<=4からA<=10を結論として先に仮定しない。
各具体stateのA<=10はDAGのchecked goodから帰納で供給する従来の構造を保つ。
同じ256閉node、同じ90CPU/90wall/4GiB capでbench改善した場合だけ旧fast全jobを閉じて置換する。
全体capはbench後に先に固定。資源上限の追加だけによる再開は禁止。
同値が破れるか改善なしならSTOPPED。初期proof/実語adapter/Audit/G5/全体checkまで分類を昇格しない。
全jobと数学unitの時間を二重計上しない。7:45/8:00の制限を守る。

## 07:38の判定

一般macro/全successors同値はLean/lint成功。256nodeが31.24→15.08wall秒へ改善。
pruned single-file全jobは560.921wall秒・4195632KiBで4GiB guard停止。このsingle-file方法はSTOPPED。
非供給tag/A11/全40候補の意味を落としていない。主張の反例ではない。
新しいA数依存layer法は64nodeのimport bench4.87wall秒/521072KiBを先に通し、同じ上限以下でH10へ切替。
数学的な修理ではなく保持環境の分割。H10最終結果前にはr4分類の昇格をしない。

## 最終全体check

final-check-2.logでactive409 library/412build jobs/2811公理宣言が成功。一般等式は監査済みのhelperで、初期Checkedのない分類reductionや証明数を独立したC1進展に数えない。数学sourceは検証時の凍結hashを保持。

## 当日journal確定実績
親cycle R-20261025-01: 06:01:21.862027〜07:59:10.380882、確認済み117分48.519秒、不足2分11.481秒。
このcardを別cycleとして加算せず、実unit/phaseの内訳は[当日DAILY](RESEARCH_HANDOFF_2026-10-25_DAILY.md)と[journal](data/daily_research/2026-10-25.json)を参照。待機・未確認・CPU・前日分の加算なし。
