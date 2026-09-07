# Hypothesis card: preload-free orbit の一歯survival比

- ID: `H-20260906-05`
- Owner: Codex
- Created: 2026-09-06
- Status: `CONJECTURED`（全z・全clockの一般命題）
- Experiment: 完了、有限結果は `COMPUTED`。範囲延長は行わない。
- Research branch: seeded survival反例 `H-20260906-04` の原因を切り分ける独立gate
- Source revision: `8a4314d7f65c728d5c6fe6584e1469de4e08332d`

## Exact statement

任意の単一初期値 `z≥0` から `a_z(0)=z`、history `{0,z}` で開始し、以後はstandardの
positive/fresh subtraction、otherwise additionを行う。0は減算の正条件により選択されないため、
`z>0` でhistoryを `{z}` とした版と軌道は一致する。任意の completed no-wrap arc 内で、
maximal prelanding runがあり、`T=1` のcomb end `(c,v)` がtest `2c+v+2` を既訪問として持ち、
同じarcに後続late landingがあるなら、`7*hPrev≤16*v`。

この一般化を検査する。`z=0`だけがcanonicalであり、他のzはcanonical反例とは呼ばない。
この問いは `E-021` の same-candidate link とは対象eventも結論も異なる。

## Why it would matter

- Frontier obligation discharged: full initial-0に固有の拘束が必要か、preloadなしでの共同生成だけが
  十分な候補かを判定する。
- Stronger than an identity: actual historyと後続landingを使うsurvival必要条件である。
- Smallest useful consequence: 1本のpreload-free反例、または有限cohortの範囲を明示したsurvival証拠。

## Provenance and dependencies

- Definitions: `arc_death_rule_probe` のrun/comb/continuedと同じ。
- Known: `H-20260906-04` のseedは比944<945に違反して59→1へ降り、事前高値blockerを3個使う。
- Unverified: generalized orbitでのsurvival比。標準全射性は仮定しない。

## Falsification plan

- Discovery: `0≤z≤1000`、各orbit `0..2,000,000` clock。
- Frozen holdout: `1001≤z≤20000`、同じhorizon。
- Small/boundary: `z=0` を既存probeとrecord単位で照合。`T=1`, `J=0`, equality、未完了arcを分離。
- Adversarial: positive initial valueだけを変更し、後からhistoryをpreloadしない。
- Repair: なし。
- Stop: completed arcで1反例を発見すればstatementを`REFUTED`にする。反例は別のset-based実装で
  clock 0からreplay。全range完了または15分で終了し、未完了orbitをPASSに含めない。
- Computation is not proof: horizonや初期値範囲の外へ一般化しない。

## Informal dependency chain

1. singleton初期値から各stepと履歴を実生成する。
2. residue increaseでarcを切り、maximal AS prelanding runとcomb末端を記録する。
3. 同じarcの後続late landingを確認後にcontinuedとし、arc completion後に採用する。
4. T=1のblocked・continued全recordでidentityとratioを整数演算で検査する。
5. 反例があればcanonical条件の必要性を示す。なければ共同birth生成を使う紙上補題が次のgate。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-06 | `CONJECTURED` | implementation前にprotocol固定 | initial-value split、horizon、15分、反例即停止を固定。 |

## Semantic audit

- Actual historyはinitial valueと過去の出力だけ。
- 比に反するterminal recordは反例ではない。後続late landingとarc完了が必須。
- canonicalのz=0とvariantのz>0を区別する。

## Final evidence

| Date | Label | Reproduction | Result |
|---|---|---|---|
| 2026-09-06 | `COMPUTED` | [exact outputs](data/strategy_2026-09-06/README.md) / [監査と論証](STRATEGY_AUDIT_2026-09-06.md) | COMPUTED: 20,001軌道を各2Mで完走。discovery 102,615・holdout 2,574,833適用record、違反0。z=0の59行は既存probeと一致。 |

## Decision

- Continue / formalize / refute / stop: 有限検査unitは完了。全z・全clockの命題はCONJECTURED、追加の範囲拡大やLean wrapperは行わない。
- Reopen only if: 共同birth生成の定量補題が紙上で得られるか、独立の反例がある場合。
