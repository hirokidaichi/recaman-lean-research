# 2026-10-03 午前の研究引き継ぎ（一般 lag の G1）

- 期間: 2026-10-03 08:09〜12:00 JST（広木さん指示「研究の現状を理解して、12時まで研究を進めて」）
- 担当: Claude Opus 5.5（親セッション）＋サブエージェント 8 本（水準構造・局所障害・窓の内部構造・C++ 反証探索・Claim N の a = 0・分類の Case 2・Claim P・R′ の Lean 化）。各エージェントの紙上主張のうち、親が検算したものはカードに明記
- 開始時 HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`。2026-10-03 午後、広木さんの指示で Sol の E-360 と本日の E-361〜E-368 を 7 コミットで着地（下記「コミットについて」）
- カード: [H-20261003-01](HYPOTHESIS_CARD_2026-10-03_GENERAL_LAG_CLOSURE.md)

## 結論（3 行）

1. line model の閉包探索で lag 23 全数・lag 27 の 2% 抽出に反例なし（E-361）。等号の場合（窓が全 phase を覆う）は p ≤ 26 で起きない（E-365）。
2. G1（全 lag）は「閉包の分類（孤立 AAS と w1 三つ組）」に、さらにそれは **Claim P「空でない閉包には被覆数 1 の S がある」** に帰着した。
   帰着は Lean 定理 `motifFull_of_private`（E-367、Claim P を仮定 hP とする条件付き定理）と、lag 一様の部品 E-362〜E-364・E-366 で形式化済み。
3. Claim P は未証明。候補は Lemma OS「成分の最古の S は被覆数 1」⟺ 保留窓 E(s₀+1) = 0。左右オートマトン（E-368）では窓長 ≤ 11 で完全に、
   ≤ 27 でも同時に開く窓 ≤ 4〜6 の範囲で成立。状態空間を lag 一様に抑える不変量が見つかれば証明になる。

## 開始時の状態

- 9/17〜9/24 の Sol 夜間週間研究で E-360 `ShortTightDonorAvoidance`（短い緊密 B は SS=2 lag-11 donor の真の最古 S を被覆しない、p 上限なし）が
  Lean 証明済み・監査済みになったが、Sol の方針で未コミットのまま作業木にあった（`SS2OldestPattern.lean`、後半カード、監査記録も同様）。
  自動化 `recam-n-1-3` は 9/24 02:33 に PAUSED。週報は「一般 lag へは新しい独立入力なしに延長しない」で終わっていた。
- G1（緊密回避 B のメンバーの lag は {3,7}）は lag-max 11 が Lean 定理（E-357〜E-359）、lag-max 15/19 が計算（E-356、19 は未監査ログ）。

## 本日の成果

| id | label | 内容 |
|---|---|---|
| E-356（追記） | COMPUTED | lag-max 19 の 4 shard ログを監査：1,636 語を順序どおり各 1 回、全 excluded。抽出 4 語を b8b970c で再実行して一致 |
| E-361 | COMPUTED | E-356 探索の C++ 移植（lag 11/15/19 と byte 一致）。**lag 23 の全 18,556 語 excluded**（凍結 holdout Q1 通過）、lag 27 の 2% 抽出 4,432 語も全 excluded。制約付き版（UP-FREE／水準／Claim N／Claim O）は lag 23 を最大 401／172／32／316 ノードで排除 |
| E-362 | PROVED-LEAN | `P2SubtractionLevelSum`：P2 窓の S の高さの和 = (L−3)/4。全 S が水準以下なら AAS、lag ≥ 7 は水準より上の S を持つ。周期語版 `past_eq_aas_of_low_subtractions` |
| E-363 | PROVED-LEAN | `P2WindowLengthBounds`：長さ ≥ 11 の P2 窓の内側に収まる P2 窓は 8 以上短い（`past_nested_gap`）、先頭 m 文字が S の P2 窓は長さ ≥ 4m+3（`past_leading_S_run_bound`、E-090 の鏡像）。最小性不要。ずれ ≤ 3 で重なる二つの P2 窓は共存しない（`shifted_p2`、`past_newer_shift`、`past_older_crossing`） |
| E-364 | PROVED-LEAN | `SuffixHallOwnerMap`：被覆された S の数 ≤ 後ろのメンバー数（suffix Hall）、有限閉包の成分で F(z) ≤ F(y+1) + 1（TOP は高々 1 段しか破れない） |
| E-365 | COMPUTED | 緊密 B の窓が全 phase を覆う（等号の場合）例は p = 6..26 の全緊密集合約 1,030 万個で 0：G1 は census 範囲で有限閉包の問題に帰着 |
| E-366 | PROVED-LEAN | `NewestMemberMotifCount`：定理 R（v 以外の所有者が AAS 型か三つ組の w1 型なら最新メンバー v の窓は AAS）。分類の強帰納の「所有 S が私有」の一段 |
| E-367 | PROVED-LEAN | `PrivateMemberMotifCount`：定理 R′（一般位置）。L ≤ 15 の数え上げと有限検査で、w1 型所有者の最新文字 S の下では窓は AAS か三つ組の w1。**帰着定理 `motifFull_of_private`：Claim P（仮定 hP、未証明）⇒ 全ての閉包は孤立 AAS と w1 三つ組の局所形** |
| E-368 | COMPUTED | 開いた窓の左右オートマトン（任意の P2 窓）：窓長 ≤ 11 の有限閉包は同時に開く窓の制限なしに E ≡ 0 で孤立 AAS と三つ組だけ（1,097 万状態中 11 状態のみ終端到達）。窓長 ≤ 15 は同時 ≤ 8 で同じ（4,286 万状態） |

紙上（カード Q2、親が検算）:

1. **周期 G1 の分解**：緊密 B の窓の和集合は周期的なので、成分は全て有限か ℤ 全体。ℤ 全体なら U = B かつ |U| = |D|（E-070 の等号の場合）。
   G1 ⟸ 有限閉包の G1 ∧ 等号の場合の G1。
2. **補題 T**（UP-FREE「各メンバーは F(own b) ≤ h_b」の下、全 lag）：有限閉包の各成分の上端は孤立 AAS か w1 三つ組。その下は lag 11 の窓が古い側へ
   伸びる「階段」になり、そこで止まる。
3. **TOP ⇒ Claim N**（UP-FREE 不要）：成分の歩みの最大値が最新メンバーでだけ達成されるなら、最新窓は AAS（E-362）。TOP は UP-FREE の最上段。
4. **補題 SI（suffix Hall）**：有限閉包の成分で #S[z, y] ≤ #M[z+1, y+1]（全 z）。⇒ F(z) ≤ F(y+1) + 1 − [σ(z)=A] − N(z, y]、TOP は高々 1 段しか破れない。
   Claim N は最新窓の先頭 A の数 a で場合分けすると、lag 15 以上では a = 0（y+1 が y を高さ 2 で所有）だけが根で残る。
5. **定理 R と分類の強帰納**（E-366 で Lean 化）：最新メンバー v の所有 S が他の窓に入らなければ M ∖ {v} は閉包で、それが孤立 AAS と
   w1 三つ組に分解すれば v は AAS。Claim N の a = 0 はこの場合に含まれる。分類の帰納で残るのは「所有 S が古いメンバーの窓に入る」Case 2。
6. **弧による高さの表示**：F(z) − F(y+1) = 1 − [σ(z)=A] − N(z, y] − D(z)（D は z をまたぐ S→所有者の弧の数）。SI の等式形。

計算で分かった構造: 制約なしの最大 lag 探索は木が lag ごとに 30〜60 倍に増える（合計ノード 303／10,026／470,371／28,920,584）。
一方、v が成分の**最新**メンバー（Claim N）か**最古始点**のメンバー（Claim O）なら、木は lag にほぼ依存しない（最大 5/8/10/32、7/32/48/316）。
「最大 lag のうち最新」だけでは効かない。**一般 lag の本体は「最大 lag のメンバーが成分の中ほどにある場合」と「上向き所有辺（UP-FREE の否定）」**。
最大 lag を仮定しない Claim N（古いメンバーの lag ≤ 23/27）も v の lag 7〜19 で全排除だが、短い v に長い所有者を許すと木は所有者 lag 一段ごとに
約 17 倍になり（v の下の構成の分類を探索しているため）、局所的ではない。E-365：緊密 B の窓が全 phase を覆う例は p ≤ 26 で 0。

## 次の一問（優先順）

0. **（最新、09:50）分類は Claim P に帰着した**：定理 R′（所有 S が私有の任意のメンバー w について、M ∖ {w} が Motif なら w は AAS か三つ組の w1。
   lag ≤ 19 は全割当の計算、一般 lag は数え上げで lag ≤ 15 に落ちる。カード 12.）により、「任意の有限閉包に被覆数 1 の S がある（Claim P）」を示せば
   メンバー数の帰納で有限閉包の分類が閉じる。R′ は E-367 で Lean 化済み（w1 型所有者の最新文字 S を仮定。`MotifOwner` にこの文字を入れて E-366 と統一するのが次の整理）。
   最小反例の形（カード 13.）：私有メンバーなし、長いメンバーを全て含む強連結な核 K（|K| ≥ 2、Back(x) = M なる x の集合）、M ∖ K は分解。
   Case 2 の上端の局所解析だけでは閉じない（どの枝も K の長いメンバーを要求する）。Claim P を最古の窓の始点 x で攻めるなら、
   σ(x) = A の場合と同じ始点の窓が 2 本の場合を扱う。
   **周期語でも帰納は直接回る**（カード 14.）：私有メンバーの軌道を丸ごと除けば周期的閉包が残り軌道数が減るので、
   G1（全 p・全 lag）⟸ 周期版 Claim P。成分が有限なら有限版で足りる。G1 と E-360 から SS=2・lag-11 donor の Gate T6 が一般 p で従う。
   Claim P の候補は **Lemma OS「成分の最古の S は被覆数 1」**（カード 15.）。所有者 lag ≤ 23 では見通し 40 以内の局所探索で成立するが、
   見通しが lag とともに伸びる。証明は moment = 0 の両側を使う必要がある（片側の不等式に緩めると私有メンバーのない閉包が実在）。最小性は不要らしい。
   さらに（カード 16.）：E 分割・D 分割補題（保留窓 E(z) = 0 なら z 以降に始まるメンバーは閉包、弧数 D(z) = 0 なら z 以前のメンバーは閉包）、
   OS ⇒ 分類の直接帰納、左右オートマトンで終端到達状態が AAS・三つ組の接頭辞 10 状態だけ（lag ≤ 27、同時に開く窓 ≤ 4〜5 の範囲）。
   残る障害は「E > 0 の核」の長さが lag に一様に有界でないこと。オートマトンの状態数を lag 一様に抑える不変量が見つかれば Claim P が閉じる。

1. **有限閉包の分類（孤立 AAS と w1 三つ組の和）をメンバー数の強帰納で示す**。最新メンバー v の所有 S が他の窓に入らない場合（Claim N の a = 0 を
   全て含む）は、v を除いた M′ が閉包になり、帰納法の仮定と**定理 R**（カード 10.：W_v の A の数え上げで m ≤ 1）で v は AAS。残るのは
   v の所有 S が古いメンバーの窓に入る場合で、ここで上端が w1 三つ組になり、三つ組を除くと閉包が残ることを示す（補題 T の UP-FREE なし版）。
   これが通れば有限閉包の G1 は全 lag で閉じ、E-365（p ≤ 26 で和集合 = ℤ なし）と合わせて p ≤ 26 の周期語の G1 も従う。
2. （済：E-366）定理 R と帰納の一段（`ClosedConfig`、`erase_closed`、`motif_of_erase_newest`）。残るのは Case 2 と、メンバー数の強帰納の組み立て（有限成分への分解を含む）。
3. 等号の場合（和集合 = ℤ）の不可能性を一般 p で示す。
4. 補助：TOP の残り 1 段（F1/F2）、UP-FREE の層ごとの証明、Claim O（下端）。

## Lean の分類の枠組み（E-366 で入ったもの）

- `ClosedConfig e M lag own`（OwnerMap・メンバーは加算・窓は P2・M2）、`Motif e M own`（全メンバーが AAS 型か三つ組の w1 型）。
- `erase_closed`：v の所有 S が私有なら `M.erase v` も ClosedConfig。`motif_of_erase_newest`：v が最新で `M.erase v` が Motif なら M も Motif。
- `pred_closed_closed`（Back 閉包）：前任者について閉じた部分列は ClosedConfig。最小反例の構造（カード 13.）の Lean 側の土台。
- `suffix_split_closed`・`prefix_split_closed`：保留窓 E(z) = 0／交差弧 D(z) = 0 で構成が二つの閉包に割れる（カード 16.）。
- 残り：Case 2（所有 S が古いメンバーの窓に入る）の上端解析と、`M.length` についての強帰納の組み立て。

## コミットについて

2026-10-03 午後、広木さんの承認（範囲：本日分＋E-360、速度制限：`RECAMAN_ALLOW_BURST=1` で 1 モジュール 1 コミットのまま連続）で次の順にコミットした。
各コミットは一時 worktree 上で「HEAD＋そのコミットまでの変更」だけを置いた状態を作り、pre-commit（構成・台帳・ハーネス G1〜G5・manifest・禁止語）を
その状態に対して通している。

1. E-360（Sol 週間研究）：`ShortTightDonorAvoidance`、`OwnerFamilyLagEleven`／`PeriodicOwnerFamilyLagEleven` の抽出、E-359/E-360 の statement audit、
   Sol のカード・引き継ぎ・週報・計画・敵対監査記録・データ
2. 本日の計算と文書：E-356 追記、E-361・E-365・E-368（COMPUTED）、`docs/data/issue73_20261003/`、`experiments/issue73_20261003/`、
   lag-19 shard ログ、カード H-20261003-01、本書
3. E-362 `P2SubtractionLevelSum`　4. E-363 `P2WindowLengthBounds`　5. E-364 `SuffixHallOwnerMap`
6. E-366 `NewestMemberMotifCount`　7. E-367 `PrivateMemberMotifCount`

`Recaman/SS2OldestPattern.lean`（H-05、13 宣言中 10 が未監査、台帳行・Audit 行なし）は意図的に**未コミットのまま作業木に残した**
（作業木の `Recaman.lean` にはその import が残る）。

## 検証

- `./scripts/check.sh`：exit 0、397 jobs、2,620 宣言、公理は `{propext, Classical.choice, Quot.sound}` のみ（E-360 の未コミットモジュールを含む作業木で）
- `bash scripts/check_research_registry.sh`：368 行、PROVED-LEAN 160、G1〜G5 は E-344 以降の 16 行全て通過
- `python3 experiments/issue73_20261003/audit_lagmax19_shards.py`：AUDIT PASS
- C++：`clang++ -O2 -std=c++17 -o mcs experiments/issue73_20261003/matching_closure_search.cpp`、`./mcs 23 40 5000000 i 8`（i = 0..7）
