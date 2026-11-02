# H-20261103-03: endpoint-Aを入力しない最後A-run非空性

Status: PROVED-LEAN（E524）、親R-20261103-01。局所探索unit、15分gate、数学探索CPU0。個別-M512/10CPU per-process/20wall、一回数学修理まで。07:45後は新探索しない。

Exact question: E521/E523と同じ全元Intp/padded/zero-fullpositive/正三run zerohead/同old target C>=4/1<=v<C/実counterから、同じ符号列の最後A長T>=1を内部供給できるか。target endpoint Aを追加仮定しない。結果を得た後にT+C=v+Rへ接続してR>Dという新strict候補削減に使う。全old history・全sourceは保持、五band不在/C1は主張しない。

弱点監査: 既存E451 three_run_free_gapはEndN targetを要し、今回のWin/P2だけから同じfのEndNを直置換できない。小境界SAAの直後の符号をSとすればWin f 0 3は真だがEndN f 0 3は偽。従ってendpoint-Aを黙って足す方法は棄却する。空最後runをgenuine四run定義で排除して結論を仮定化してはならない。

新chain: gはtarget clock qだけAへ変更し、全strict prefix<qでは元fと等しい。Winは端点より前だけを使い、EndN/cNは計数範囲より前のprefixだけを使うことを独立補題で供給。gの既存E451を使い、頭部/供給/free数を元fへ厳密に戻してT0を矛盾させる。基点0/pとtarget開始tは保持し、gを別orbitや元履歴の代替として仮定しない。反例ならprefix-invarianceが破れた正確な窓/endpointを保存する。

受入はactual T>=1又はR>Dという次の判断を変えるedgeと元p adapter、G5/Audit/fullcheck。prefix extensionality helperだけ、既存三runの再証明、target-A付きに弱めたadapterは不可。15分でedgeなしならSTOPPED、残時間は元target/最後source平方と実free課金の別機構へ。旧stopped計算や大表を再開しない。

06:19:10受入: strict-prefix Win/EndN/count preservation、SAA境界、既存E451を消費するWinだけの3run gap、actual T>=1/R>Dと元p adapterまで同-M512/G5/Audit/fullcheck634jobs3390宣言PASS。人間レビュー未。T0を仮定で切らず、元履歴へ全countを戻した。三runの分類/Qを再実行せず既存定理を消費して前提を弱化した入力edge。最初のtoy decideはWin unfold不足で失敗、同じliteral/同上限で展開して成功。旧停止jobは再開せず親cycle継続。
