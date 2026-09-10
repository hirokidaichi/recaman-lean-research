# 2026-09-09：連続加算から供給窓を調べた1時間研究

**方針を変える根拠が得られた。** 既存のlag-11/15の結果を足場に残し、
窓長ごとの型表を増やす方法から、連続加算と窓同士の重なりを一様に扱う方法へ進めた。
長さに上限を置かない下界・間隔制約・一般容量拡張をLeanで証明した。
一方、「加算が続く間は最小供給lagも増える」という推論には、任意に長い区間で反例がある。

**全lagの供給容量E-070、全加算同時供給の排除E-067、全射性・非全射性は未証明。**
今回の容量拡張が扱うのは下界を達成する窓の一群であり、それ以外の長い窓が残る。

- 開始：2026-09-09 07:46:45 UTC（16:46:45 JST）
- 終了：2026-09-09 08:41:18 UTC（17:41:18 JST）、約55分
- 基準revision：`8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`
- 実施：一人のagentで提案・反証・形式化・監査を順に分離。外部送信・commit・pushはしていない。
- 前の先読み反証E-089とは別の研究時間。そちらの出力は変更していない。

## 得られた結論と証拠

Aを加算（+1）、Sを減算（−1）とし、窓は新しい符号から並べる。
P2とは、長さdの過去窓について `Σ ε_i=1` と `Σ i ε_i=0` が同時に成り立つこと。
符号語上の供給条件であり、その語がRecamánの実軌道で生成されることは主張しない。

| 仮説カード | 判定 | 最も強い結果 |
|---|---|---|
| [H-03：先頭A数と供給距離](HYPOTHESIS_CARD_2026-09-09_LEADING_RUN_SUPPLY.md) | `PROVED-LEAN` E-090 | 先頭m≥3個がAなら **d≥4m−1**。全mの等号・最小P2族も証明 |
| [H-04：等号窓の分類](HYPOTHESIS_CARD_2026-09-09_SHARP_PARTITIONS.md) | `PROVED-PAPER` E-091 | d=4m−1の全窓はmの整数分割と一対一。続くm−1個のSは別途Lean |
| [H-05：入れ子供給の間隔](HYPOTHESIS_CARD_2026-09-09_NESTED_SUPPLY_GAP.md) | `PROVED-LEAN` E-092 | k回のAを挟む入れ子窓には **Δ(Δ−4k)≥4k(d−1)**。従ってΔ>4k |
| [H-06：長い等号窓の容量拡張](HYPOTHESIS_CARD_2026-09-09_SHARP_CAPACITY_EXTENSION.md) | 一般定理 `PROVED-LEAN` E-095、既存写像への適用 `PROVED-PAPER` E-093 | 半径Lの短い供給の単射に、m≥max(3,L+1)の等号窓をまとめて追加できる |
| [H-07：最小lagの単調増加](HYPOTHESIS_CARD_2026-09-09_NONNESTED_LAG_DROP.md) | `REFUTED` E-094 | 一回のAで23→15。具体例はLean、任意に長いA区間の反例族は紙上 |

### 新しい容量拡張の意味

等号窓には、先頭のm個のAの直後に少なくともm−1個のSがある。
このA区間の直前から二つ目のSを供給先に割り当てる。
入れ子間隔の不等式により同じSを二つの等号窓が使うことはなく、
m≥L+1なら既存の短い供給の割り当てもこのSには届かない。
周期のつなぎ目をまたいでもこの二点が保たれることと、個数の上限までLeanで確認した。

既存の短い規則には「lag 3を3個前のSへ送る」という条件が必要で、φ7/φ11/φ15はこれを満たす。
従って紙上で、任意の周期について次が成り立つ。

```text
|lag≤11の供給A| + |m≥12, d=4m−1の供給A| ≤ |S|
|lag≤15の供給A| + |m≥16, d=4m−1の供給A| ≤ |S|
```

後者で新たに扱うlagは63,67,71,...と無限に続く。ただし、同じlagでも等号条件を持たない
窓は含まない。一般拡張のLean定理に対する既存φ7/φ11/φ15の具体的適用は紙上に残した。
155行のlag-15表をLean化したり、lag-19の型表を追加したりはしていない。

### 一般化を止めた反例

新しい方から並べた `AAASSSASSSSAAAAAAASASSS` は先頭がAAAで、最小P2 lagは23。
先頭にAを一つ付けると最小lagが15になる。両時点での全ての短いprefixをLeanで確認した。

さらに任意r≥2について、先頭A数がr²−1でも

```text
最小lag：4r²+4r−1 → 4r²−1   （一回の加算で4rだけ短縮）
```

となる反例族を紙上で証明した。正符号和3、周期4r²+4r+1の語にも埋め込める。
よってA区間の長さの閾値を上げても単調lag案は修理できない。
この族は、入れ子条件を勝手に外す推論を反証する。E-070の反証は得ていない。
具体的な25周期例では、全lagの供給Aは5個、Sは11個で、容量を破らないことも別途確認した。

## 再現・検証

全ての新しい計算は探索範囲とholdoutを事前に分け、任意符号語・境界・弱めた仮定も試した。
各出力にrevisionとscript hashを記録し、[証拠bundle](data/issue73_20260909/README.md)へ保存した。

| 検証 | 結果と制限 |
|---|---|
| 先頭A数の下界 | d≤15で探索、d=19でholdout。違反0。全mの根拠はLean証明 |
| 等号族 | m=3..16と17..128の全prefixを確認。全mの最小性もLean |
| 分割分類 | 別々の生成法でm=1..24の全窓集合が一致。全単射の証明は紙上 |
| 入れ子間隔 | 宣言したtailを全数検査。適用例0のセルは支持証拠と数えない |
| 保護S | L=11で7,143窓、L=15で6,654窓。短い接触は(j,d)=(4,3)のみ |
| lag短縮 | r=2..8、holdout r=9..64で全prefix確認。別実装で正符号周期への埋め込みも照合 |
| 反例の範囲監査 | r=2の25周期例は全lag solverと直接replayが一致。供給A=5≤S=11 |
| Lean全体監査 | **1,265宣言が合格**。今回20宣言を監査に追加。具体的23→15証人は公理依存なし |

主な実行コマンド（repository root）：

```sh
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/leading_run_supply.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/sharp_partitions.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/nested_supply_gap.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/sharp_capacity_extension.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/nonnested_lag_drop.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/verify_nonnested_periodic.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/verify_lag_drop_scope.py
lake env lean Recaman/LeadingRunSupply.lean
lake env lean Recaman/SharpPeriodicSupply.lean
./scripts/check.sh
shasum -a 256 -c docs/data/issue73_20260909/SHA256SUMS
git diff --check
```

新しい第2moduleを追加した後に全体checkを再実行した。
最後の結果は [one_hour_check.txt](data/issue73_20260909/one_hour_check.txt)。
実際の型署名と文章の対応、特に既存Uの単射だけを仮定していることは
[意味監査](data/issue73_20260909/semantic_audit.md)に記録した。
有限計算に違反がなかったことを一般証明として使用していない。

## 変更したものと残した境界

- [LeadingRunSupply.lean](../Recaman/LeadingRunSupply.lean)：下界、等号族、S block、入れ子間隔、保護S、具体的反例。
- [SharpPeriodicSupply.lean](../Recaman/SharpPeriodicSupply.lean)：周期接着、単射、非衝突、一般の有限容量拡張。
- `Recaman.lean`、`Recaman/Audit.lean`、`docs/MODULE_IMPORT_CONTRACTS.tsv`：importと監査へ統合。
- 上記5仮説カード、7実験script、出力・hash bundleを追加。
- README、current frontier、証拠台帳E-090〜E-095、proof map、portfolio、用語集を更新。
- 既存の未追跡 `recaman-visualizer/` は変更していない。

境界反例はm=2のAAS、P2の片方の式を落としたAAASS／AAAASSSA、
長いrun条件を落とすと保護Sが既存φ11と衝突するm=4,5の例、そして23→15のlag短縮。
実装中の失敗は主に整数castとlist indexの正規化で、仮説を弱める修理はしていない。

## 次の判断

**型表の延長・先読み回数の増加・run長だけの単調lag修理は停止を維持する。**
次の数学的作業は、まず等号から一段外れた `d=4m+3` の窓について、
同じA区間での重なりと、短い供給に使われないSが残る条件を調べること。
受入条件は全mで使える不等式・割り当て規則、または明示的な反例。
窓長ごとの表の追加だけになったら停止する。

形式化だけを進めるなら、E-095に既存φ7∪φ11を代入することが次の有界作業になる。
これ自体を全lag研究の突破とは数えない。非等号窓と入れ子でない切り替わりを同時に扱う
新しい制約は、依然として未解決である。
