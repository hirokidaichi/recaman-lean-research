## 02:00枠: 凍結 core W/Q の E-360 登録

結論: 3-symbol の限定 E-360 登録案は独立意味監査と隔離 G1-G5 を通過した。対象は
`w1_owns_oldest`、`w1_next_addition`、`short_tight_avoids_ss2_donor` のみ。W は4フィールドの
`OwnerFamily` を明記した条件付き局所定理、Q は正周期・nodup/tight/current-A・最小 P2
lag 3/7/11 の B と最小 lag-11 SS=2 donor に限る。一般 lag/Gate T6、後半定理、
`SS2OldestPattern`、実軌道、E-070/E-067、Recamán列の全射性へ広げない。

初稿の2-symbol行は W の `own t=t-7` を引用しなかったため文書不整合として差戻し、旧版とhashを
保存した。`w1_owns_oldest` を加えた修正版は数学source・仮説・結論を変えておらず、数学的な修理ではない。
昼の形式化前入口監査欠落と01:00 checker初回source/raw欠落も解消したことにしない。

隔離 `/tmp/recaman-registration-0200.WgTYMy/repo` に提案 registry、公式配置形 G5、frontier、
proof map を配置して検査した。G1-G5 11行、protected 4行、registry 360行 / PROVED-LEAN 155行、
module reachability 389/389、import contracts 110、full check 392 jobs、公理監査2572、全て exit 0。
vacuity は0/21、lintは20/21 substantive。後半21定理全体の意味認証とは扱わない。

カード2本、registry、G5、CURRENT_FRONTIER、PROOF_MAP、本handoffの適用前全文と提案全文、source
hash、正確な command/timeout/output、独立監査判定を slot0200 に保存した。保護ラベル、Lean source、
gate は変更しない。次の判断は、適用版の全hashを独立監査者が再照合した後にこの限定登録を確定するか、
不一致ならカードを `CONJECTURED` のまま保つこと。一般 lag の探索は別の入口監査を要する。
