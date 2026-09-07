# Hypothesis card: #61 clock 112 exclusion from certified deep trace

- ID: H-20260907-03
- Owner: Codex
- Created: 2026-09-07
- Status: `PROVED-LEAN`（`E-060`、既存定理の結合と意味監査を完了）
- Base revision: ad3367a
- Role order: proposer → falsifier → formalizer → auditor（同一agentが順次実施）
- Branch: 停止済みのfloor探索の拡張ではなく、#61の既存certificateの結合と完了判定

## Exact statement / acceptance

```lean
{target start : Nat} {parent : PhaseSearchNode}
{source : PermanentTailDischargeReturnCertificate target start parent}
(r : TerminalExactDischargeReplayCertificate source) :
r.crossingTime ≠ 112
```

既存の112≤r.crossingTimeと結合して113≤r.crossingTimeを得る。
新しいoracle、future-low witness、coverage、trace検証結果を追加仮定にしない。
主要定理をAuditへ登録し、root/import契約と証拠台帳を同期し、`./scripts/check.sh`を通す。
#61の完了条件の第一選択肢「少なくともclock 112を無条件排除」を満たす。

## Known and informal dependency chain

1. `onehundredfourteen_le_target`: 任意の同型replayで114≤target（PROVED-LEAN）。
2. crossingTime=112なら、`FirstAt a 371 4825`からhistorical minimum clock=4825。
3. 同じreplayの`no_low_witness_at_or_after_4825_of_crossingTime_eq_112`は、
   4825≤wかつa w≤targetからFalseを返す（PROVED-LEAN）。
4. `GeneratedBalancedTrace99734.generated_value`: a 99734=19（PROVED-LEAN、Audit登録済み）。
5. w=99734では4825≤wかつ19≤114≤target。従ってclock112は排除される。

最小の新規補題は上の直接的な結合。target=223のpinningも利用可能だが不要であり、
そのcertificateを追加でimportしない。statementの仮定を増やすことによる回避はしない。
新しい定義・rank・wrapper・deep traceの再生成は不要。

## Falsifier before formalization

- 正準数列をPython setで0..99734まで一度replayし、既知の端点371@4825、19@99734と、
  clock108..113の局所配置を独立に点検する。計算は証明の入力にしない。
- 境界: 4825自体は371なのでtarget223以下のlow witnessではない。w=99734とtarget18/19の
  閾値も検査する。時間順序は有限整数の直接比較である。
- 弱historyモデル: 4825まで正準prefixを保ち、その後の値を371に固定する列では、
  target223のfuture-low witnessは出ない。これは漸化式を満たさず、端点371の認証だけでは
  本結合を代替できないことを示す対照である。
- 局所crossing at112自体は正準prefix内に存在する。排除対象はpermanent-tailの全前提を
  持つreplay certificateであり、「数列にclock112がない」という主張ではない。
- Discovery/holdout: 新しい統計的仮説を探索しないため適用しない。範囲と端点は既存の
  認証済みstatementから固定した回帰監査で、未使用holdoutとは呼ばない。

## Stop

補題のsource/target型が一致しない、または追加のfuture-history前提が必要なら、
具体的な型の差を記録して#61は開いたままにする。clock777へ向けた列挙や新しい大域不変量の
探索には広げない。証明が通れば同じstatementの意味監査とfull checkで完了判定する。

## Why this matters / limits

既存の数値証明と一般的なno-low補題を結合し、GitHubに残っていた一つの具体的残余を閉じる。
portfolioの停止判定を覆す一様機構の発見とは扱わない。全射性・非全射性・survivalの状態は維持する。

## Evidence log and decision

結論：#61の第一完了条件を満たした。追加仮定なしにclock112を排除し、replayのclock下界を
113、target下界を115へ更新した。最も強い証拠は次の3宣言のLean kernel検証と公理監査である。

`Recaman.TerminalExactDischargeReplayCertificate` namespace:

- `crossingTime_ne_onehundredtwelve`: `r.crossingTime ≠ 112`
- `onehundredthirteen_le_crossingTime`: `113 ≤ r.crossingTime`
- `onehundredfifteen_le_target`: `115 ≤ target`

| 日付 | label / 検査 | command | 結果 |
|---|---|---|---|
| 2026-09-07 | `COMPUTED`、固定境界の回帰監査 | `python3 experiments/clock112_closure_audit.py` | first371=4825、19@99734、局所crossing112、target18/19境界、弱history対照を確認 |
| 2026-09-07 | `PROVED-LEAN`、最小consumer | `lake env lean Recaman/PermanentAboveClock112Exclusion.lean` | 初回で3定理が通過。数学statementの修理なし |
| 2026-09-07 | import削除の負の対照 | [再現手順](data/issues_2026-09-07/issue61/README.md) | 2 direct importはそれぞれ削除時にcompile失敗 |
| 2026-09-07 | repository監査 | `./scripts/check.sh` | 265 library modules、24 import契約、268 build jobs、1,220宣言の公理監査がPASS |

計算のsource revision、SHA-256、正確な出力と検証記録は
[`data/issues_2026-09-07/issue61/`](data/issues_2026-09-07/issue61/README.md)に保存した。

## Semantic audit

- 非形式的主張→形式的statement：任意の`target/start/parent/source`と、そのsource上の完全な
  replay証明書を量化する。clock112という値だけを排除し、新しいhistory・oracle・low witnessを
  引数に要求しない。正準の`a`とsourceのpermanent-tail条件は既存型に保持されている。
- 形式的statement→意図した帰結：既存の112下界と112の排除から113下界が出る。
  既存の`r.crossingTime + 1 < target`から115下界が出る。113が実現可能という主張はしない。
- 空虚性の範囲：clock112を持つ完全なreplay型が空であることが今回の意図した結論である。
  すべてのclockでreplay型が空、または任意の局所crossingが不可能とは主張していない。
- 弱い読みの反例：正準列には`a 112 = 152 < 223 ≤ 265 = a 113`という局所crossingが実在する。
  4825まで正準で以後371一定という列では、371の初出だけを保ってfuture-lowを失える。
  この列は4826で漸化式に違反する（正準値5197）。従ってprefix認証だけでは証明を代替できない。
- 依存の監査：target=223のpinningは不要だった。より広く適用できる既存の114下界で十分であり、
  結論を弱めたり前提を増やしたりする変更ではない。witnessの時間順序`4825 ≤ 99734`と値の
  順序`19 ≤ 114 ≤ target`を明示してno-low補題へ渡している。
- 失敗・反例：意図したstatementの反例は出ず、修理は不要。上記の負の対照は、局所crossingや
  prefixだけへstatementを誤読した場合の反例である。Python出力はLean証明の入力にしていない。

## Changes and next decision

- Lean：`PermanentAboveClock112Exclusion.lean`を追加し、rootとAuditに登録した。
- 再現：境界監査script、実行出力、source hashes、import削除手順を保存した。
- 文書：evidence registry、current frontier、proof map、strategy map、roadmap、module architecture、
  development log、READMEを同期した。
- 判定：#61を完了扱いにする。coverage表の生成やclock777までの一括排除は証明していない。
  停止済みのfloor列挙を延長せず、大域A/B枝と正のsurvival枝の停止判断を維持する。
- 残る不確実性：全射性・非全射性、canonical survival、および全clockに対するreplay排除は未解決。
  次の研究unitには、既存portfolioの再開gateを満たす独立した数学的入力が必要である。
