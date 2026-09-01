# 並列証明スプリント — 2026-09-01 午後

## 実施枠

- 開始: 2026-09-01 13:46 JST（基準コミット `5baf9c3`）
- 終了: 2026-09-01 17:00 JST
- 方式: 5系統並列（Lean形式化×3、紙上分析×1、exact probe×1）→直列統合、を3ラウンド

> **結論:** 全射性そのものは未証明のまま。residual kernelの両枝を精密化し、
> B枝（unbounded right-terminal stream）の残余を「無限個のupward resetの返済」へ、
> A枝（eventual-high corridor）の残余を「自給自足供給窓の無限持続の排除」へ、
> それぞれexactに絞った。副産物として、canonical軌道の無条件の運動法則を2つ
> （純加算rayの不可能性、長さ2加算runの不在）発見・証明した。全成果は
> `SharpResidualKernel`の受け渡し証明書に束ねた。check.shは1103宣言で緑、
> 公理集合は`{propext, Classical.choice, Quot.sound}`のまま。

## 1. B枝の前進 — Gate 3〜5の完全Lean化

Round 16の6-gate分解（`PARALLEL_RESIDUAL_DECOMPOSITION_2026-09-01.md`）のうち、
紙上可能とされていたGate 3〜5を形式化した。

### 1.1 blocker床と天井脱出（`TargetStreamBlockerUnbounded`）

- `blocker_floor`: streamのuniversal no-escape（右entry床）は、anchor補題
  `entry_below_or_anchor_le_blocker`により**blocker床** `root ≤ blocker` へ持ち上がる。
- `exists_blocker_gt` / `exists_entry_gt`: `Classical.choose`で「前episodeのfinal timeより後」を
  再帰的に選ぶ時系列chainを構成し、final time単調性→単射性→`Fin (B+2)`制限→
  one-use鳩の巣`exists_blocker_gt_of_many`で、blockerとentryが任意の天井を超える。

### 1.2 無限upward reset（`TargetStreamUpwardResets`）

- `exists_upwardReset_after`: consecutive macro pairの二択
  `a s₂ < blocker₁ ∨ blocker₁ < blocker₂`で、左枝では`blocker₂ < a s₂ < blocker₁`と
  blockerが厳密降下するため、blocker値のstrong inductionが停止し、任意cutoffの後に
  必ずupward reset（右枝）が起きる。
- `exists_upwardReset_entry_le_after`: reset点では`a s₁ ≤ blocker₂`（前fresh intervalは
  新blockerの左に完納）も保持。
- `eventualHigh_or_infinitelyManyUpwardResets`: 大域kernelは
  「corridor ∨（rooted stream ∧ 無限upward reset）」へ精密化された。

**帰結:** B枝の残余は、`RESET_REPAYMENT_AUDIT_2026-09-01.md`で`STOPPED`のまま保存されている
reset repayment予想（各resetについて`target occurs ∨ later entry < blocker`）の、
無限個のresetに対する排除だけになった。返済が一つでも起きれば`blocker_floor`との整合が
問われる形へ、問題は完全に局所化されている。

## 2. A枝の前進 — corridorの構造法則と自給自足性

### 2.1 無条件: 純加算rayの不可能性（`EventualHighCorridorStructure`）

`no_perpetual_forcedAddition_ray`: canonical軌道が時刻M以降ずっとforced additionを
続けることはできない。ray上の値は毎歩その時計だけ増えるため、(i) ray値はpre-ray hull
`upperTri M`を有限時間で追い越し、(ii) ray内の隣接値は2以上離れ、(iii) 加算直後に露出する
candidateは常に「直前値−1」なので、witness時刻`p = M + upperTri M + M + 2`で
candidateがfreshかつ時計条件を満たし、合法減算が可能になって矛盾する。

系`exists_canSubtract_of_ray`（任意のMの先に合法減算がある）は分岐に依存しない恒久資産である。

### 2.2 corridorの運動法則

- `corridor_subtraction_lands_above_clock`: corridor内の合法減算は
  `target + clock + 2`を超えるfreshな値に着地する（着地の次candidateが高いままであることの言い換え）。
- `infinitely_many_high_fresh_landings`: 2.1と合成し、A枝は**clock超えの高位fresh着地を無限個**強制する。
- `corridor_forcedAddition_candidate_seen`: corridor内のforced additionは時計不足では起きず、
  必ず「candidateが既訪問」によって起きる。

### 2.3 自給自足供給窓（`EventualHighCorridorSupply`）

- `corridor_value_law`: corridor内の全時刻で`target + clock + 1 < a n`（軌道は対角線+targetの上）。
- `corridor_infinitely_many_forcedAdditions`: 永久減算rayは値を毎歩2以上下げるため
  value lawと矛盾し、forced additionも無限個再発する。
- `corridor_forcedAddition_supplier`: candidateがpre-cutoff hull `upperTri cutoff`を超える
  forced additionの供給者（candidateと同じ値を持つ時刻t）は必ず`cutoff < t ≤ n`にあり、
  供給値自身がvalue law（`t + 1 + target < 値`）とhull上界（`値 ≤ upperTri t`）に従う。

**帰結:** 無限corridorは有限seedを除いて**自給自足系**である。任意有限長のseeded corridor
no-go（`SeededHighCorridorNoGo`）は有限preloadで動くため、この構造は有限seed論をくぐり抜ける
最初のcanonical固有入力（generation-vs-reuse chronology路線の第1レンガ）になっている。

## 3. 無条件の新法則: 長さ2の加算runは存在しない（`NoDoubleAdditionRun`）

1e9 exact probe（§5）が発見した「加算run長histogramに長さ2の空白がある」を即日Lean化した。

- `double_forcedAddition_candidate_returns`: 合法減算の直後に加算が2連続すると、
  次のcandidateは`a(n) − (n+1) + (n+2) + (n+3) − (n+4) = a(n)`、
  すなわち**減算前の値そのもの**へ戻る。
- `double_forcedAddition_extends`: その値は既訪問なので、3回目の加算が強制される。
  ゆえに減算に挟まれた長さちょうど2の加算runは存在しない。

## 4. 受け渡しkernel（`SharpResidualKernel`）

`SharpCorridor`（candidate床・value law・fresh着地列・forced addition再発・供給窓）と
`SharpResetStream`（認証済みseparator root・blocker床・天井脱出・entry interface付きupward reset）の
2つのProp構造体を定義し、`MissingPermanentAboveTail.sharpResidualKernel`が仮想反例を
どちらかの証明書へ送る。以後の研究サイクルはこの2構造体だけを消費すればよい。

## 5. exact probe（`experiments/corridor_structure_probe.cpp`、1e9項）

| 計測 | 結果 |
|---|---|
| 加算run長histogram | 1: 499,935,267 / **2: 0** / 3: 11,957 / 4: 6,012 / 5: 951 / 6: 13 |
| 最長run | 5 (1e6) → 6 (1e7〜1e9)。成長の兆候なし |
| 減算着地のcone分類 | cone-exterior率 ~43%で毎decade定常。excess中央値 ~0.6n |
| low-candidate率 | 毎decade再入するが希薄化（decade 8で7×10⁻⁸）。candidate=mexはdecade 5以降絶滅 |
| mex | 1355でclock 1e6〜1e9の間凍結 |
| blocked additionの燃料年齢 | ancientFrac（age ≥ n/2）~0.376で定常。最大age ~0.99n |

解釈: (1) 長さ2の空白は§3で無条件に説明された。(2) 実軌道はlow-candidate regimeへ
全スケールで再入し続けており、A枝の「low candidateの停止」は実軌道の姿ではない
（ただし頻度は指数的に希薄化しており、反証もできない）。(3) 加算runは伸びず、
corridorの燃料は恒常的に古い履歴から供給されている。

## 6. 紙上分析

### 6.1 Q-A: liminf二分法とrigid recurrence（A枝の主発見）

corridorのcandidate walk `d(m) = a(m) − (m+1)` は「発散する」か「有限のliminf `c > target` を
非有界に再訪する」かに二分される。後者で `c` を非有界再訪する最小値に取ると、遅い各use clock
`m`（`d(m) = c`）は次の3点を強制される。

- (P-a) `c` は既訪問で、時刻 `m+1` は**forced addition**（減算すると次candidateが`0 < target`となり回廊が壊れる）
- (P-b) 時刻 `m` への入りは**合法減算**で、`a(m) = c + m + 1` は対角線上のfresh初出
  （加算だと`a(m−1) = c + 1`が回廊の床を割る）
- (P-c) `c + m` は時刻 `m+1` までに**既訪問**でなければならない
  （freshなら`m+2`で着地し`d(m+2) ≤ c − 3 < c`がliminf床を割る）

(P-c)のper-use需要は本質的に新しいsupply/demand対象で、pre-corridor履歴でもstream自身の
entryでも満たせず、自己供給は倍化clock格子`m = 2m′ + 2`上のforced-addition出力に限られる——
seeded no-go族の`upperTri`骨格を、canonical軌道自身が**生成**しなければならない形である。
有限seedはこのパターンの有限部分しか演じられないため、無限corridorのこの帰結は
seeded no-goを構造的にくぐり抜ける。

### 6.2 Q-A: A枝は第二の永久欠損値を強制する — Lean化済み

`valuesThrough m` の長さは `m+1` なので、窓 `[0, m + target + 1]`（要素数 `m + target + 2`）には
少なくとも `target + 1` 個の未訪問値がある。corridor value lawは時刻 `m` 以降の全軌道値を
`target + clock + 1` 超に置くため、窓内の値には将来の着地機会が存在しない（凍結）。
未訪問値のうちtarget以外の1つを取れば、**A枝では `target < u` なる永久欠損値 `u` が存在する**。
計数は証人の構成に使われ、矛盾の導出には使われていない（no-go 6は適用外）。
Round 4で`EventualHighCandidateTail.exists_second_missing`
（`EventualHighCorridorSecondMissing`）としてLean化した。初回コンパイル一発通過。

紙上ではさらに、欠損値 `u` に相対化した候補規律（遅い`u`-low候補は既訪問を強制される）から、
**A枝は「candidate walkの発散」∨「最小再訪候補でのrigid recurrence」へ縮約される**ことを確認した。
発散残余 `a m − m → ∞` は自由事実ではない（実軌道は`a 99734 = 19`のように低値へ遅く着地する）。

### 6.3 Q-B: strip凍結の棄却とblocker birth分類の停止

セッション中に提案された「strip凍結」（B枝で軌道がいずれroot以上に留まる）は、
値帯`[0,E]`への着地が無条件に高々`2E+2`回である自由事実の言い換えと判定し、棄却した。
その上でblocker birthを (0) pre-tail有限 / (E) 旧entry再利用（右ladderの生息域、排除はSTOPPED中の
gated no-return） / (H) high-born `b > birth + target` に完全分類したが、導出可能な不等式
（high-born blockerは使用combのstartより前に生まれる）はladderが満たせるため、
**B枝への非自由入力は今回得られなかった**。B枝はGate 3〜5の形式化成果で保存し、
reset repaymentの新invariant待ちとする。

## 7. birth分類（`EventualHighCorridorBirth`）

供給定理を候補値の**初出**（birth）へ強化し、birthステップを無条件に二分した。

- `corridor_forcedAddition_birth`: 供給者は候補値の初出時刻に取れ、初出もcorridor窓内
  （`cutoff < t`、cone不等式、hull上界）にある。
- `firstAt_succ_birth_dichotomy`（無条件）: 正の時計での初出は実ステップが産む。
  減算なら「前時計のsubtraction candidateが実際に取られた」、加算なら「加算出力で自分の時計を上回る」。
- `corridor_forcedAddition_birth_classified`: 遅いforced additionのcandidateは、corridor内部の
  birth時計`t+1`で、(i) 時計`t`のcandidateが取られた減算、または (ii) 時計`t`の加算出力として
  生まれた。どちらでもbirth時計は`candidate − target − 2`より小さい。

減算birth枝では候補値が「より早い時計自身のcandidate」なので、この分類は原理的に反復でき、
candidate ancestry chainがcorridorを後方へ歩く。chainの出口は加算birthか有限pre-cutoff hullに
限られる。この反復の形式化が次の研究対象である（本ラウンドでは1ステップのみ記録）。

## 7b. Round 4 — 第二欠損値とrigid recurrence（紙上分析のLean化）

### `EventualHighCorridorSecondMissing`

§6.2の定理を完全Lean化した。`valuesThrough_length`（履歴は1時刻1値）、
`EventualHighCandidateTail.exists_second_missing`（**A枝はtargetより上の第二の永久欠損値を強制**）、
`missing_not_unique`（`target_missing`と同形の否定存在版）。計数段はrangeリストの
Nodup部分集合長で閉じ、凍結段はcorridor value lawの1回適用＋omegaで閉じる。

### `EventualHighCorridorRecurrence`

§6.1のrigid recurrenceのpayloadを明示仮定の下でLean化した。

- `corridor_recurringCandidate_forcedAddition`: use clock（`d(m) = c ≤ m`）からの一歩はforced addition
- `corridor_recurringCandidate_entry_subtraction`: use clockへの一歩は合法減算で、
  対角値`c + m + 1`へのfresh着地
- `corridor_recurringCandidate_successor_seen`: 床`c ≤ d(k)`の下で後続値`c + m`は既訪問が強制される
- `corridor_recurringCandidate_event`: 3点を束ねたrigid event
- `corridor_candidate_bounded_recurrence`: 有界再訪から単一の非有界再訪値を抽出（K帰納法）

### `EventualHighCorridorDichotomy`（Round 5、A枝capstone）

§6.1の二分法を無条件のLean定理にした。`exists_least_recurring_candidate`（最小再訪値の構成）、
`exists_uniform_bound_of_no_recurrence`（帯`(target, c)`の一様回避境界）を経て、

- `candidate_diverges_or_recurrence`: **発散 ∨（最小再訪候補`c > target`が床`c ≤ d(k)`を張り
  任意に遅く再訪する）**
- `diverges_or_rigidEventStream`: 右枝では任意に遅いuse clockで完全なrigid event
  （`d(m)=c`、対角fresh減算入り`a(m)=c+m+1`、forced addition出`a(m+1)=c+2m+2`、
  後続値`c+m`の既訪問強制）が発動する

A枝の残余はこれで「発散残余の排除」と「event streamの需要`c+m∈履歴`の供給injectivity」の
二点へ正確に分かれた。

### `DivergentCandidateMissing`（Round 6、発散枝の代償）

発散側の逃げ道に値段をつけた。candidate床`K < d(m)`（m ≥ N）は値法則`K + m + 1 < a(m)`を
与え、窓`[0, N + B + 3]`の将来着地を全排除する。履歴の1時刻1値計数により窓上部`(B, N+B+3]`に
未訪問値が残り、それは永久欠損である。ゆえに

- `divergent_candidates_missing_unbounded`: **発散するcandidate walkは任意の限界を超える
  永久欠損値を残す**
- `missingUnbounded_or_rigidEventStream`: A枝の最終形——**欠損値非有界 ∨ rigid event stream**

仮想反例のA枝は、「欠損値集合が非有界」という大きな構造的代償を払うか、rigid event streamの
需要を無限に自己供給し続けるかのどちらかしかない。

## 8. 分岐スコアの更新

| branch | 前回 | 今回 | 根拠 |
|---|---:|---:|---|
| A枝 eventual-high corridor discharge | 12/100 | 30/100 | 二分定理まで到達（value law・無限fresh高位着地・自給自足供給窓・birth分類・第二欠損値・rigid event stream）。残余は「発散排除」と「需要`c+m`の供給injectivity」の2点 |
| B枝 reset repayment | 15/100 | 15/100 | 今回は再開せず。ただしB枝残余はGate 5形式化により「無限個のupward resetが全て未返済」へexact化され、攻撃面は縮小 |
| sharp kernel architecture | — | 90/100 | 受け渡し証明書として完成。以後の研究はこれだけを消費 |
| 無条件運動法則（ray不可能・run長2禁止） | — | 恒久資産 | 分岐に依存しない |

## 9. 検証

- `./scripts/check.sh`: 通過（build 241 jobs、公理監査1121宣言、禁止語0）
- 許可公理: `{propext, Classical.choice, Quot.sound}`のみ
- 新規11モジュール（239 .leanファイル、66,717行）すべて初回`lake env lean`一発通過、
  統合時の再検証で問題0件
- 新規human-proofレポート11本、viewer manifest: 239 modules / 164 reports
- probe: C++20 `-Wall -Wextra -Wpedantic -Werror`でコンパイル、1e5でPython独立実装とexact一致を確認
- 計算結果は仮説選択にのみ使用し、Lean定理の仮定にはしていない

## 10. 追記: Round 7（burst合成）

`RecurringCandidateBurst`で、rigid eventの successor demand `c + m ∈ 履歴` が2本目の
forced additionへそのまま変換され、`NoDoubleAdditionRun`（§3）が3本目を強制することを示した。
無条件の運動法則が仮想分岐の内部で実際に仕事をした最初の例である。A枝の最終合成は

```text
欠損値非有界
∨
需要 c+m 1個あたり加算3連burst（c+2m+2 → c+3m+4 → c+4m+7）の無限event stream
```

である（`EventualHighCandidateTail.missingUnbounded_or_burstStream`）。

最終検証: build 242 jobs、公理監査1124宣言（`{propext, Classical.choice, Quot.sound}`のみ）、
240 .leanファイル・66,831行、human-proof 165本、check.sh緑。

## 11. 追記: 実軌道の再利用candidate probe（`candidate_reuse_probe.cpp`、1e8項）

burst stream理論のper-use需要（use clock `m` ごとに後続値 `v + m` の既訪問）を、実軌道の
positive-blocked reuse 21,718,335件で観測した。

| 計測 | 結果 |
|---|---|
| 再利用inventory | distinct使用値13,161,685、最大20回使用 |
| use-gap比率 | 連続use比の76〜78%が1.1未満（狭い時計窓に密集）。倍化帯（1.5〜3）は10〜14%のみ |
| 後続需要の充足率 | decade 7で0.036%、減衰 ≈ m^(−1/2)。burst streamは100%充足が必要 |
| birth halving | addition-born供給の62.6%が`w/2`未満の初出（理論の方向と一致するが弱い）。subtraction-born供給が59%で優勢 |
| 最多使用値 | step-3の等差comb（値≈1.86×初使用時計、使用窓の時計比~1.22） |

解釈: 実軌道の再利用は「generic＋comb幾何」であり、burst streamの自己供給格子
（倍化clock、100%継続）とは似ても似つかない。仮想A枝のrecurrence枝は、実軌道が一度も
示さない機構でしか維持できない——「不可能である」証明への期待を支持する観測である。
ただしこれは経験則であり、Lean定理の仮定には使っていない。

## 12. 追記: 敵対的セマンティック監査（Round 8）

新規12モジュールの頭書き定理に対して、free-conclusion攻撃・仮定整合性攻撃・
statement-vs-intent攻撃・数値スポットチェックを実施した。結果:

- **偽・空虚な定理は0件**。value law（`a 99734 = 19`のkernel認証済み反例で仮定の実効性を確認）、
  第二欠損値（B枝ではcomb railが窓内に着地するため凍結が壊れることを確認——corridor仮定が実効）、
  発散仮定（Lean上で反証も証明も不能な誠実なconditionalであることを確認）、二分定理の否定押し込み、
  burst、upward reset群、いずれも仮定を正しく背負っている。
- **無料ルート2件を検出・修理**: (1) `corridor_infinitely_many_forcedAdditions`の結論は無条件に真
  （減算の時計条件だけで永久減算rayは不可能）。(2) `corridor_forcedAddition_candidate_seen`の
  結論も無条件に真（時計不成立なら候補は`0 = a 0`に切り詰められ常に履歴内）。
  両者を`UnconditionalStepRecurrence`として誠実な名前で記録し、corridorの真の寄与
  （時計条件の成立＝ブロックは純粋に履歴由来）を`corridor_forcedAddition_clock_and_seen`として
  復元、過大主張していたdocコメントを修正した。副産物として
  **canonical軌道の両ステップ種が無条件に無限再発する**ことが揃った。
- `NoDoubleAdditionRun`は実軌道2000項で検証: sub-add-add出現26回すべてで3本目の加算が発生、
  sub-add-add-subは0回。

過去に3度踏んだ「生成証明書を保持しない忘却形は必ず捏造される」の教訓どおり、
敵対的検査は今回も通常の証明作業では見つからない指摘を返した。
