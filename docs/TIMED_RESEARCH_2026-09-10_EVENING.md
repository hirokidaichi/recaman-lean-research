# 2026-09-10 19:46–24:00 計測つき研究

開始 19:46:42 JST。終了予定 24:00 JST。壁時計を記録する。

## 経過

| 時刻 | 内容 |
|---|---|
| 19:46 | 開始。H-31 孤立 a=0 直前 S × E-128 |
| 19:52 | 周期スキャン完了。直前 S は周期13で衝突 |
| 19:58 | 双対 AAS 兄弟を Lean 化。軌道 10^7 で共同 3950 件 |
| 20:04 | singleton 修理は発見1..16で0、holdout 17で51件。課金停止 |
| 20:07 | E-135..E-137、入れ子 one-per-run k=1 Lean。check.sh 通過 |
| 20:10 | case5 長さ23まで0。孤立 a=0 は軌道上すべて NoSAAS |
| 20:12 | k≥2 入れ子は mass≤-2 で Lean |
| 20:16 | E-140 NoSS mass1 の 2M+n≥3。check.sh 通過（1656宣言） |
| 20:22 | case5 語レベルと連続 stream の短い残りを Lean。孤立 a=0 の非singletonは10^7で5件 |
| 20:27 | 再開。equality family の最小対を Lean 化 |
| 20:37 | E-142 Lean 通過。SS=3 extra 6件はすべて E-140 moment、先頭 SA |
| 20:42 | check.sh 通過。1670宣言、143証拠、E-142/E-143 登録 |
| 20:43 | 標準10^7のSS=2に minWord extra 0/17443。lead=1は11件すべて ASA |
| 20:52 | NoSS mass1 完全分類 Lean。SS=3 extra はすべて (SA)^k ++ minWord |
| 20:55 | (SA)^k minWord の slack 3+8k を Lean。check.sh 147証拠 60 PROVED-LEAN |
| 20:58 | SS=2 の glue prefix+(SA)^k minWord は 10^7 で 0（E-147） |
| 21:00 | チェックポイント。孤立 a=0 の非singleton 5件はすべて E-135 の長さ3 run（E-148） |
| 21:03 | SS=4 は 16,455 件、one-per-run 0（E-149） |
| 21:08 | SSヒストグラム。clean同士run違反41件はすべて gap2 の E-135 |
| 21:12 | E-151：孤立先頭の後続 t+2 が clean であることを Lean |
| 21:18 | 高SS同一run 20組。18件は gap1 で extra mass1 moment=1-|v|、NoSSではない（E-152） |
| 21:28 | NoSS mass1 の slack は 3+8k+4a。MassOneNoSS ↔ NoSS∧mass1 |
| 21:21 | equality-family / minWord 周期は E-070 反例にならない。minWord は U=0（E-153） |
| 21:24 | 孤立 singleton の lag はすべて 3 mod 4（52,193件）。P2 の ones 偶数から従う既存恒等式 |
| 21:32 | 孤立 singleton の SS 間隔は gap1=40434、gap5=10、≥8=11749。2..4と6,7は0（E-154） |
| 21:40 | E-155：gap2 は SSSS で ssCount≥3。check.sh 155証拠 62 PROVED-LEAN |
| 21:48 | E-156：逆入れ子 extra の mass/moment は SS 非依存。check.sh 156証拠 63 PROVED-LEAN |
| 21:38 | 孤立 singleton は 52178 が SA 始まり、15 が SS 始まり（E-157） |
| 21:45 | SS=2 の先頭 run は 0,1,3 のみ。a=3 が companion 148件すべて。a≥4 は0（E-158） |
| 21:55 | E-159：NoSAAS SS=2 の先頭 A は 5 未満。a=4 が残る穴 |
| 22:01 | 22:00 チェックポイント。E-160：a=4 等号族は moment≤-8 で P2 でない |
| 22:20 | E-161：NoSAAS SS=2 の先頭 run は 4 未満。残る 0,1,3 は軌道と一致 |
| 22:28 | SS=3 の先頭 run は 0,1,3,4。a=4 が 54 件（E-162）。SS=2 の a=4 禁止は SS 特有 |
| 22:50 | E-161 を任意語の先頭 A run 判定へ接着。check.sh 162証拠 66 PROVED-LEAN |
| 22:35 | SS=4 先頭 run は 0,1,3,4（E-163）。E-164：a=5 族は P2 でない |
| 22:23 | 再開。次unitは NoSAAS なしの SS=2 AAAA |
| 22:28 | 長さ≤19の自由語と a4 族 pqr≤20 は P2 ヒット0 |
| 22:32 | E-166/E-167/E-168 Lean。NoSAAS を SS=2,3 先頭上限から除去 |
| 22:35 | 等号族 2·moment 公式を 33887 語で確認。P2 ヒット0 |
| 22:39 | E-169：ssCount≥1 なら先頭 A run ≤ SS+1。等号族 moment≤-3 |
| 22:43 | 抽象最小 NoSAAS SS=2 a=0 は gap 3,7 を持つ。E-154 は語定理ではない |
| 22:46 | E-170：NoSAAS の SS 間隔4は ssCount≥3 |
| 22:51 | E-172：NoSAAS ssCount=2 の gap 6 は内部 AAAA |
| 22:54 | 孤立 SS 始まり15件の語。8件 SSS(SA)* gap1、7件 SS(SA)* gap≥17 |
| 22:56 | E-174：SSS 始まり SS=2 の尾は NoSS |

## 安定した判定

- E-135 / E-151 `PROVED-LEAN` 孤立先頭の clean 兄弟。clean 同士の run 違反41件はこの形
- E-136 `REFUTED` 直前 S 課金と singleton 修理。E-148 の5件は E-135 の長さ3 run
- E-137 `PROVED-LEAN` 入れ子 one-per-run。E-142 で無制限は抽象反証
- E-140 / E-145 / E-146 `PROVED-LEAN` NoSS mass1 の下界・分類・(SA)^k minWord
- E-142 `REFUTED` 無制限連続 one-per-run（最小対 Lean 認証）
- E-143 / E-147 / E-149 / E-150 / E-152 / E-154 `COMPUTED` 軌道の SS 構造
- E-155 `PROVED-LEAN` SS 間隔2は ssCount≥3
- E-159 / E-160 / E-161 `PROVED-LEAN` NoSAAS SS=2 の先頭 A run は 0,1,3。a=4 族は moment≤-8
- E-166 / E-167 / E-168 `PROVED-LEAN` NoSAAS なし。SS=2 先頭<4、SS=3 先頭<5、一般先頭≤SS+2
- E-169 `PROVED-LEAN` ssCount≥1 なら先頭 ≤ SS+1。等号族は 2·moment≤-6
- E-067 / E-070 は未解決。minWord 周期は U=0 で反例にならない（E-153）

## 未完（24:00まで継続中）

無制限 one-per-run は抽象で反証済み（E-142）。軌道の SS=2 は 10^7 で違反0のまま。
SS=2 先頭 run は 0,1,3（E-166）。孤立 singleton の S 配分は課金再開せず未解決。
E-067 / E-070 は未解決。
