# Hypothesis card: 任意finite prefixを含むsurvival反例族

- ID: `H-20260906-07`
- Owner: Codex
- Created: 2026-09-06
- Status: `PROVED-LEAN`
- Research branch: `H-04/H-06`で得た反例を、停止判断に十分なparametric countermodelへする

## Exact statement

任意の有限集合 `F⊆Nat` に対し、Fを初期historyに含み、cardinality・triangular range・canonical
current parityを満たすexact seeded orbitに、`T=1` blocked comb endで
`16v<7hPrev`かつ同じno-wrap arcの後続late landingを持つ例がある。さらにl3blocked後から
そのlandingまでのpositive blockerは全て一回だけ使用される。

凍結する構成は、正の偶数 `w>max(F)`、偶数 `D≥10` で `D²-8D>w` を取り、
`v=D²+w`, `J=v/2`, `h=v+1+3J`, `n=16h+[h odd]·2`, `b=n-2`, `c=n+2J+1`。
初期値 `x=3n+h-1`、seedは

```text
F ∪ {0,x,v-1} ∪ {v+3j : 1≤j≤J}
  ∪ {(j-2)c+v+j(j-3)/2 : 4≤j≤D}.
```

符号語は `SS (AS)^J S A^D S^D`。comb end `a(c)=v` の後、`a(c+2D)=w` に着地する。
Fの全要素より高いwを選ぶので、特定の既知小値をseedから除くことに依存しない。
F inclusionは「Fの末尾からboundaryまでcanonicalに接続できる」ことを意味しない。

## Why it would matter

- Local recurrence、one-use、seed density/parity、任意の固定finite prefix inclusionを同時に課しても
  survival ratioが出ないことを示す。canonical-only命題の反証ではない。
- 「known value 1をseedに足せば直る」というH-04の弱さを明示して解消する。
- 次の候補にはcutoffを固定した有限前史追加ではなく、全必要blockerの共同生成を拘束する入力が必要。

## Falsification plan

- Discovery: canonical prefix horizons `0,4,128,1000` のF、上式の最小偶数w/D。
- Frozen holdout: prefix horizons `10000,200000`。構成式・定数・suffixを変更しない。
- Independent replay: Python setで最終seedを固定し全stepを再生。全符号・no-wrap・run・landing・
  seed bounds・parity・F inclusion・l3blocked後のpositive blocker多重度を検査。
- Boundaries: strict `D²-8D>w`、`w>maxF`、prelanding run直前の余分なq=2値もfreshness除外へ含める。
- Repair: なし。構成式が1例でも破れればfamilyを`REFUTED`、紙上証明を撤回。
- Stop: 紙上の全history membership証明と凍結holdoutを完了、または反例・15分cap。

## Informal dependency chain before formalization

1. Prefix `SS(AS)^JS`の値集合を、level-1 railとlevel-2 rail（最初のSS由来の1値を含む）に分ける。
2. `A^D`のcandidateは二つ前のaddition出力より1小さい値で、j≥4は明示seedにある。
3. その後k回減算した値は `A_(D-k)-k²`。同levelのpreloaded candidate `A_(D-k)-1`とは一致しない。
4. q=2でprelanding railを飛び越す条件がちょうど `D²-8D>w`。q=1も既存railの下へ出る。
5. 最後はwで、Fより上、全small seedより下なのでfresh。residue総費用はD²でv-D²=w>0。
6. `J=v/2`から `7h-16v=3v/2+7>0`。各positive blockerは異なるlevelにあるため再利用しない。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-06 | `CONJECTURED` | familyと全parameterを実行前に固定 | arbitrary Fとone-useを同時に要求。 |

## Semantic audit

- Boundary以前のF以外のseed要素のfirst-birthを供給していないことを明示する。
- 論理的に反証するのはseeded survival比であり、canonical E-045ではない。
- 反例はmembershipの自由度を使い、survivalや未来のlandingを仮定しない。

## Final evidence

| Date | Label | Reproduction | Result |
|---|---|---|---|
| 2026-09-06 | `PROVED-PAPER` | [exact outputs](data/strategy_2026-09-06/README.md) / [監査と論証](STRATEGY_AUDIT_2026-09-06.md) | 任意有限Fのパラメータ族について全history membership・freshness・no-wrap・seed boundsを紙上で証明。固定prefix horizons 0,4,128,1000,10000,200000の独立replayもPASS（E-056）。 |

## Decision

- Continue / formalize / refute / stop: 紙上証明とholdoutを完了。一般族のLean化を独立した有界作業としてissue化する。
- Reopen only if: 一般族のLean化はissue #70の別unit。正のsurvival攻略の再開にはfamilyを分離する共同birth/history不等式が必要。

## 2026-09-07 completion

#70で全payloadの一般族をLean認証した。詳細は[形式化カード](HYPOTHESIS_CARD_2026-09-07_ISSUE70_FORMALIZATION.md)。
E-056をPROVED-LEANへ更新。正のsurvival攻略の再開gateは変更しない。
