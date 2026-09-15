# Hypothesis card: the oldest-subtraction characterization of tight subsets（G1 の骨）

- ID: `H-20260915-20`
- Created: 2026-09-15 18:50 JST
- Status: `COMPUTED`（E-349）。紙上証明は §4 の骨組みまで。Lean は Hall 増分補題（E-351 予定）から
- Research branch: issue #73、研究計画 P2（[RESEARCH_PLAN_2026-09-15.md](RESEARCH_PLAN_2026-09-15.md)）
- Probe: `experiments/issue73_20260915/tight_structure.cpp`（E-345 と同じ列挙、Hall が U 全体で成り立つ正符号和語の necklace 代表、
  **donor を固定せず U の全部分集合**を走査）。Output: `docs/data/issue73_20260915/tight_structure.txt`（p = 8..26、6.4 秒）

## Exact statement

E-345 と同じ設定。U = 最小 P2 窓を持つ供給 phase、N([v]) = v の最小窓内の減算 phase、`oldestS(v)` = v の最小窓で最大 offset の減算 phase
（E-348 の `oldestOffset`）。B ⊆ U が緊密とは |N(B)| = |B|。凍結した問い：

```text
OS  緊密 B では v ↦ oldestS(v) が B 上で単射で、その像がちょうど N(B) に一致するか
T   緊密 B のメンバーの lag は 3 または 7 に限るか（lag ≥ 11 の窓は緊密部分集合に入らないか）
W2  lag-7 メンバーの窓は w1 = SAAAASS に限るか（w2 = ASAASAS は入らないか）
SIB w1 メンバー u の lag-3 兄弟 u−3（phase u−6 を被覆）は常に B に入るか。u−1 の所有者は誰か
```

受入条件：wordsWithHighSS 等は E-345 と同じ列挙なので E-179 と整合（同じコード経路）。OS は「最古 S が相異なる」と「集合が N(B) に一致」を別々に数える。

## Results（p = 8..26、緊密部分集合の総数は p=22 で 280,868、p=26 で 5,126,692）

| 事実 | 結果 |
|---|---|
| **OS** | 全 p で全緊密部分集合が満たす（例外 0） |
| **T** | lag ≥ 11 のメンバーを持つ緊密部分集合は 0 |
| **W2** | lag-7 メンバーは全件 w1、w2 は 0 |
| **SIB** | w1 メンバーの兄弟 u−3 は全件 B に入る。u−1 は全件「別のメンバーの最古 S」で、その所有者は全件 lag 3（AAS at u+2）。w1 の private phase は全件 u−7（自身の最古 S） |
| 補助 | 全緊密部分集合が lag-3 メンバーを含む。サイズは p=26 で最大 7 |

## Decision

- G1 は次の形で定式化し直す：**G1′ = OS**。OS から T・W2・SIB が従う（§4）。G2（ss=2 donor の最古 S は緊密回避 B に被覆されない）は
  OS の下では「donor の最古 S が B の別メンバーの最古 S になる」ことの否定に帰着し、E-348 の lag-7 分類と lag-3 の既存補題で閉じる見込み。
- Lean の第一歩は donor に依存しない **Hall 増分補題**：緊密 B と x ∈ U∖B について N([x]) ⊆ N(B) なら Hall が破れる、すなわち
  N([x]) ⊆ N(B) を満たす x は B に入る。SIB はこの補題の直接の系（兄弟 u−3 の唯一の phase u−6 は u の窓内）。

## 4. 紙上証明の骨組み（未完、ここまで確定）

記法：語は周期 p の巡回語。窓は弧。「新しい／古い」は各窓の内部でのみ使い、大域順序は使わない（巡回性のため）。

**補題 A（Hall 増分）**。B 緊密、x ∈ U∖B、N([x]) ⊆ N(B) ⇒ 矛盾。∵ B∪{x} は U の部分集合で |N(B∪{x})| = |N(B)| = |B| < |B|+1。
系 A1（SIB 前半）：w1 メンバー u ∈ B の兄弟 u−3 は AAS（e(u−4)=e(u−5)=A, e(u−6)=S, e(u−3)=A）で N([u−3]) = {u−6} ⊆ N([u]) なので B に入る。
系 A2：e(u+1)=e(u+2)=A なら AAS at u+2 も B に入る（N = {u−1}）。

**補題 B（各メンバーの private phase は高々 1）**。B 緊密、v ∈ B ⇒ v だけが被覆する phase は高々 1 個。∵ Hall を B∖{v} に適用。

**補題 C（最古 S の所有）**。OS の「像 = N(B)」側：任意の s ∈ N(B) に対し oldestS(v) = s なるメンバー v がある。
証明方針：s を被覆するメンバーの集合 C ≠ ∅。各 v ∈ C の窓で s は「ある offset」にあり、s より古い S を持たないメンバーがあれば完了。
全 v ∈ C が s より古い S を持つと仮定して矛盾を導く。ここで使うのは、v ∈ C の窓の「s より新しい部分」に S が無い場合（s が v の newest S）
に限れば、v の newest 側の A-run 長 a_v が 2 以上なら AAS at s+3 が U にあり（e(s+1)=e(s+2)=e(s+3)=A）、補題 A で B に入る、という議論。
**未完の部分**：a_v ∈ {0,1} の場合（w1 型・w2 型・d 型の先頭）と、s が v の newest S でない場合の処理。census は前者が緊密性と両立しないことを
示す（w2 は緊密集合に一度も現れない）が、その理由は P2 最小窓の先頭 A-run の分類（E-132/E-166：SS=2 で {0,1,3}、E-090：run m≥3 ⇒ lag ≥ 4m−1）
と組み合わせた有限の場合分けになる見込み。

**補題 D（最古 S の単射性）**。v ≠ v′ ∈ B で oldestS(v) = oldestS(v′) = s なら矛盾。方針：両者の窓は s より古い部分が全て A なので、
一方の窓が他方の窓の s 以前の部分を含み、短い方の窓が長い方の「s より新しい部分」の接頭辞になる… ここも最小 P2 窓の接頭辞非 P2 性で
閉じる見込みだが未完。

**T の導出（OS を仮定）**。lag 4m+3 ≥ 11 のメンバー u の 2m+1 個の S は全て N(B) の元で、OS により各々が相異なるメンバーの最古 S。
u 自身の最古 S 以外の 2m ≥ 4 個は他メンバー w_i の最古 S で、w_i の窓は u の最古 S より新しい位置から始まり、開始から s_i まで全て A。
すると w_i の窓は u の窓と「S の直後に A が続く」区間で重なる。lag-11 の 7 語（E-348）で各非最古 S の直後 3 bit を見ると AAS 所有者は
最大 1 個しか置けず、残りの S は w1 型所有者（S S A A A A S の形を要求）を要するが、その形は donor 語の bit と衝突する——この有限検査を
7 語 × 4 個の S について機械的に行えば lag 11 は落ちる。lag 15 以上は E-090 型の run 制約で帰納する。**ここが P2 の本体。**

## Stop conditions

- OS/T/W2/SIB のいずれかが p ≤ 31 で破れたら、G1′ を弱め（例：「lag ≤ 11」）て再設定する。
- 補題 C/D の a_v ∈ {0,1} 場合分けが 2 unit で閉じなければ、OS を `CONJECTURED` の gate として置き、G2 を「OS を仮定した条件付き」で先に Lean 化する（claim に仮定を明記）。
