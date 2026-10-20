# 2026-10-20 夜の研究引き継ぎ（Claim P → 区間容量予想 H）

- 期間: 2026-10-20 19:43〜（広木さん指示「今から時間を見て5時間ほど研究をすすめて」「そのまま続けて、時間いっぱいまで進めて」）
- 担当: Claude Opus 5.5（親セッション）＋サブエージェント（monovariant・levels・oldest・satsearch・hpot・hinduct・hunclean・htrunc・vform・df2・pump・
  auditEq と Lean 担当 leanH・leanClean・leanLowSS・leanUnclean）。紙上の主張は親が検算したものだけを定理として登録した
- 開始時 HEAD: `75491ee`（E-367）。Sol の `Recaman/SS2OldestPattern.lean` は今回も未コミットのまま作業木に残した（コミットの間だけ退避）
- カード: [H-20261020-01](HYPOTHESIS_CARD_2026-10-20_LINE_CAPACITY.md)

## 結論（3 行）

1. Claim P（閉包に被覆数 1 の S がある）は、**区間容量予想 H**「任意の ±1 語の任意の区間で、区間内に収まる P2 窓の終点になれる A の数 ≤ S の数」の
   **等号の場合の分類**と同じ問題だった。H は中心予想 E-070 の非周期・有限の強化（E-370 で H ⇒ E-070 を Lean 化）。
2. H は lag 一様には未証明。証明できたのは「clean な窓」（Lean、E-371・E-373：深さ 1・SS 対 ≤ 1 を含む）の区間と、
   窓長 ≤ 31 に制限した場合（計算機援用、E-372・E-374）。
3. 計算機援用の帰結：**窓長 ≤ 31 の有限閉包は幅によらず孤立 AAS と三つ組の和**、**lag ≤ 31 の緊密 B の lag は {3, 7}**（G1 の lag 制限版、全周期）。
   反例があるなら長さ 35 以上の P2 窓が必要。

## 注意：origin/main との分岐（push していない）

ローカル main は origin/main に対し ahead 14・behind 40。merge-base は `08c0856`（2026-09-16）。origin 側には codex の PR #85〜#89
（2026-10-01〜10-11、SS2 donor・NoSAAS）が入っており、**E-360〜E-371 が両側で別の主張に使われている**。ローカルの 10/03 と 10/20 の
コミットは一度も push されていない。統合（番号の付け替え・別ブランチでの PR など）は広木さんの判断待ち。

## 今夜の成果

| id | label | 内容 |
|---|---|---|
| E-369 | COMPUTED | 予想 H を長さ ≤ 34 の全語で確認。H の下で閉包＝等号の場合、EqClass（(SAAA|SSAAAASAAA|A)*）を長さ ≤ 31 で確認 |
| E-370 | PROVED-LEAN | `LineCapacityPeriodic`：H（仮定）⇒ 周期語で任意 lag の供給 phase 数 ≤ 減算 phase 数 |
| E-371 | PROVED-LEAN | `CleanWindowCapacity`：clean な窓の始点は S、同始点の 2 窓の新しい方は unclean ⇒ endable が全て clean な区間で H |
| E-372 | COMPUTED | 窓長 ≤ 31 の H を全語で確認（有限状態グラフ、独立実装 2 本）。H+ は長さ 34 で偽 |
| E-373 | PROVED-LEAN | `LowSSCleanWindow`：最小窓は深さ 1 か SS 対 ≤ 1 なら clean（E-128 の区間版の拡張） |
| E-374 | COMPUTED | EqClass_L を全幅で検査（タイトなポテンシャル道、L ≤ 31。周期版も L ≤ 31）。窓長 ≤ 31 の閉包の分類・lag ≤ 31 の G1 |
| E-375 | PROVED-LEAN | `UncleanWindowStructure`：unclean な最小窓は面積正の最後の戻り r の直後に SS を持ち、その前に高さ h+1 からの最後の減算 q |
| E-376 | PROVED-LEAN | `CapacityEqualityInduction`：密度補題と H の帰納段。**H（⇒ E-070）は EqClassW（等号の場合がブロック語）だけに帰着** |
| E-377 | PROVED-LEAN | `SingleWindowEquality`：EqClassW の帰納段の場合 (B)（区間全体が 1 本の P2 窓）は SAAA しかない（定理 B） |
| E-378 | PROVED-LEAN | `BlockSuffixPositivity`：ブロック語＋A^a の接尾辞は mass・面積とも ≥ 1、S の連の後の A は区間内の窓を持たない、TS₁ |

## 否定的結果（再提案しないこと）

- 水準ごとの H（深さ 2・高さ 2 で偽）、符号和を落とした 1 次元版、窓内の正準写像による単射（最古 S・最新 S など全て衝突）、
  target 点 Q_b の単射性、clean → 始点の固定を unclean へ延長すること（長さ 28）、H+（長さ 34）、DF2（長さ 32）、
  開いた始点の和に分解するポテンシャル（LP の Farkas 証明書）、窓ごとの単調量（SC 用）、moment の片側緩和。

## 次の一問

0. **はみ出し補題 SL**（a_y + d(q0) ≤ 2 なら X ≤ d(q0)）。**d = 0 は紙上で証明済み**（straddle・sl01）、**d = 2 は補題 TS から従う**
   （TS：S だけを挟んで隣り合う endable な 2 つの A の前で不足 ≥ 3、長さ ≤ 34 で成立、TS₁ は Lean 化済み）、**d = 1 は S1（はみ出しの窓は k1 から始まる、データのみ）に帰着**
   （補題 T・定理 R1・命題 V、S1 ⇒ S2（capret）、a_z ≠ 2 なら y = SAAA、a_z = 2 は s1proof が紙上で閉じた。**残りは a_z ≠ 2 での S1**）。
   要再検算：SL の d = 1 の部品、s1proof の j = 4 の場合分け、eqstep の補題 BW・C の手での上界（いずれもサブエージェントの申告のみ）。詳細はカードの「SL」節。EqClassW の帰納段の場合 (B) は E-377 で排除済み、場合 (A) は SL から定理 B を y に適用して従う（カード）。
   以下は SL に至る前の整理：**EqClassW の帰納段**（E-376 で H 全体がここに帰着）。最小反例は x = w·A^i·y（w はブロック語、y の内部で不足 d > 0、
   w のブロック境界は全て y で終わる窓にまたがれる、最後の 2 つの endable の間は A だけ）。長さ 35 以上の窓が必要（E-374）。
1. **H の lag 一様な証明**（0. と同値）。道具：Clean Window 定理（clean は始点に単射）、unclean の構造（E-375）、U1/U3（水準付きの照合、長さ ≤ 34 で成立）、
   U1 型の水準で切った H、D2-local（深さ ≤ 2 の照合、長さ ≤ 34）。照合は「深さ ≥ 3 の clean だけが始点から動けばよい」（U1-R2）。
2. **圧縮補題**：DL4（任意の語に e − s を減らさない連続 4 文字の削除がある、長さ ≤ 30 で成立）は H を含意する。正準的な削除規則は全て失敗。
3. EqClass の lag 一様な証明（H の下で Claim P と同値）。
