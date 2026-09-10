# Hypothesis card: latest periodic-supply approach review

- ID: `H-20260909-01`
- Owner: Codex, review of committed research
- Created: 2026-09-09
- Status: `STOPPED` for further lag-by-lag enumeration; existing E-080/E-086 retained
- Research branch: issue #73, audit only
- Source revision: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Conclusion and bounded question

直近の研究は有効な部分定理を増やしたが、全lagに共通する規則は得ていない。
次はlag別の表を増やす方法から、履歴長に依存しない割り当て規則または
ポテンシャルの検討へ切り替える、という既存の停止判断を支持する。
全射性・非全射性の見立てを、この結果だけで更新する根拠はない。

今回の一問は「最新の定理と反証記録は、lag-by-lagの続行を正当化するか」。
受入条件は、主要Lean statementの量化・意味を確認し、有限核と停止判定を再現すること。
その確認で終了し、新しいlag・periodの列挙には進まない。

## Exact statements and dependencies

任意の整数p>0とp周期符号列ε: Z→{−1,+1}について、AとDは一周期内の加算・減算phase。
加算phase t がP2供給を持つとは、ある整数d≥1で
`Σ(i=1..d) ε(t−i)=1` かつ `Σ(i=1..d) i ε(t−i)=0` が成り立つこと。

- E-080 `PROVED-LEAN`: `|U7|+|U11min|≤|D|`。周期長の上限はない。
- E-086 `PROVED-PAPER`: `|U7|+|U11min|+|U15min|≤|D|`。
- E-070 `CONJECTURED`: 正符号和の周期語で、全lagの供給phase集合Uについて `|U|≤|D|`。
- E-067 `CONJECTURED`: 正符号和の周期語には供給を持たない加算phaseが少なくとも一つある。

E-070ならE-067、E-067とE-065の紙上縮約なら有限履歴実更新のeventual固定符号周期を排除できる。
ここから全射性や非全射性への接続は得られていない。全lagの容量はE-067より強い目標であり、
短いlagの容量を増やしたこと自体はこの未知の接続を解消しない。

## Four-role review and falsification

- Proposer: E-080/E-086が全lagへ延長できる機構を提供したかを問う。
- Falsifier: 既存17型・155型と、宣言済みセレクタ群の反証検査を再実行。
  3つのφ7境界型を確認し、実軌道由来を仮定しない符号窓での衝突判定を確認した。
  新しい探索・holdoutではなく、凍結済み証拠の再現である。
- Formalizer: 新Lean実装なし。`p2At_iff_P2`、`minLag11At`、計数定義、最終定理、Audit登録を照合。
  P2の二式からd≡3 (mod 4)なので、11未満では3と7の除外で最小lagの意味が合う。
- Auditor: 有限型の検査と任意周期への接着を分け、E-088の停止範囲を確認した。

## Evidence log

以下はすべて上記revisionで実行。Pythonには `PYTHONDONTWRITEBYTECODE=1` を指定。

| Command | Exact relevant output | Interpretation |
|---|---|---|
| `./scripts/check.sh` | `Axiom audit: 1245 declarations, all within {propext, Classical.choice, Quot.sound}.` / `All Lean builds and audits passed.` | 既存の `PROVED-LEAN` 証拠を再検証 |
| `python3 experiments/issue73_20260908/lag11_verify_independent.py` | `U7_UNCONFLICTED=[]` / `OPEN_COLLISION_PAIRS=0` | `COMPUTED` 再現、既存有限核を支持 |
| `python3 experiments/issue73_20260908/lag15_verify.py docs/data/issue73_20260908/lag11/lag15_csp.txt` | `raw_lag15=263` / `min_lag15=155` / `N_UNBLOCKED=0` / `OPEN_COLLISION_PAIRS=0` | `COMPUTED` 再現、E-086をLean証明へ昇格しない |
| `python3 experiments/issue73_20260908/uniform_selector.py` | lag15 `open_pairs`: min=14, max=8, median=12, closest_d2=10 | `COMPUTED` 再現、宣言済みセレクタは継続gateを通らない |

完全な既存出力は [第2pass bundle](data/issue73_20260908/README.md) に保存されている。
今回の全体監査ログは `/tmp/recaman-approach-review-20260909-check.log`。

## Semantic audit and remaining uncertainty

周期長が無制限であることと、供給lagが無制限であることは別である。
E-080のLean statementは前者だけを証明しており、文書の限定された主張と一致する。
E-088は宣言したセレクタ候補の失敗と研究資源の停止判断である。
任意の共通規則の不可能性、全lag容量の反証、実軌道の反例を得たわけではない。
既存φ7/φ11の割り当てを変更する可能性も含め、一般の方法は未排除である。

## Decision and handoff

今回の変更はこの監査カードのみ。既存定理・証拠label・frontierは変更しない。
停止済みのlag表延長を再開する根拠は得られなかった。

少し進める次回の単位は、新しい全lag候補を一つだけ式にして、既知の反例で先に落とすこと。
現時点ではその式を得ていないため、新しい証明枝をactiveとはしない。
割り当てなら155型を新たな型表なしで通すこと、ポテンシャルなら
`SSAAAAAASSS`の供給加算で必要量だけ増え、`AAASAASSSSS`への減算追加で高々1しか減らないことが
最初のgateである。これは必要な反証検査であり、通過だけで全lag証明とはしない。
候補が型表・有限ベクトルの再包装に戻るならそこで終了する。
