# Hypothesis card: survival反例の固定prefix stress test

- ID: `H-20260906-06`
- Owner: Codex
- Created: 2026-09-06
- Status: `COMPUTED`
- Research branch: `H-20260906-04` の意味監査。既知の小値を欠くseedだけに依存していないか
- Source revision: `8a4314d7f65c728d5c6fe6584e1469de4e08332d`

## Exact statement

`H-20260906-04`の59→1反例は、canonicalで既出の1をseedに含めていない。この制限を隠さず、
一回だけ次の強いcountermodel探索を行う。`F=valuesThrough(128)`を独立replayで固定し、
H-04と同じseed grammarに `F⊆seen` を追加する。全future transitionのexactness、seedの
cardinality・triangular range・current parityを維持したまま、同じarcで後続late landingを持ち、
`16v<7hPrev` を満たす `T=1` countermodelがあるか。

これはH-04で反証された一般命題の修理ではない。countermodelの適用範囲を監査するstress testであり、
H-04のseedがcanonical到達可能と主張することを禁止する。

## Why it would matter

- `1∈history`だけで消える反例を、full canonical provenanceの障害と過大評価しない。
- 既知finite prefixを含めても反例があるなら、有限の小値membership補修だけの限界を示せる。
- 固定prefix Fを含むことは、seed全体がcanonical prefixであることとは異なる。

## Falsification plan

- Small/boundary: H-04反例へ1を追加するとwordが破れることを確認。
- Discovery: `10≤v≤80`、H-04と同じ最小Jとn、`F⊆seen`。
- Frozen holdout: `81≤v≤160`、同じ条件。
- Node cap: 各vで100000。時間cap: 15分。
- Acceptance: fixed seedから全stepを独立replayし、F inclusionと後続late landingとno-wrapを保存する。
- Stop: 最初の証人、全range完了、node/time cap。さらにprefixや定数を変更するrepairはしない。
- 未発見は一般定理としない。canonical反例とは呼ばない。

## Dependencies / informal chain

1. 0からclock128までのcanonical値集合Fを作る。
2. H-04のrequired seedにFを加え、既存forbidden subtraction targetsとの非交差を確認する。
3. H-04と同じno-wrap signed-word探索と、最終seedからの独立replayを行う。
4. 反例の後続landingがFに含まれないことを確認する。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-06 | `OBSERVED` | H-04証人のseed inspection | seedに1がなく、終点は1。H-04だけではfull-provenance必要性の証拠にしない。 |
| 2026-09-06 | `CONJECTURED` | stress test実装前にprotocol固定 | F、v range、node/time capを固定。 |

## Semantic audit

- Exact seed continuationは維持するが、prefix128とseed boundaryの間の経路は与えない。
- 接頭辞集合を含むことだけではjoint first-birthのprovenanceにならない。
- 反例のsmall-value hole、survival threshold、history multiplicityを全て表示する。

## Final evidence

| Date | Label | Reproduction | Result |
|---|---|---|---|
| 2026-09-06 | `COMPUTED` | [exact outputs](data/strategy_2026-09-06/README.md) / [監査と論証](STRATEGY_AUDIT_2026-09-06.md) | F=valuesThrough128を含むseed143値でc=2883,v=76,J=33,h=176から2901で5へ着地、1216<1232。最初の証人で停止しholdout探索は不要となった。 |

## Decision

- Continue / formalize / refute / stop: 完了。finite prefixを足すだけの修正では不足。一般化は別カードH-07で検査。
- Reopen only if: frozen条件の内側で証人または紙上のno-goが得られた場合。
