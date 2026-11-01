# terminal三runを続ける第四rayのlocal profile

- ID H-20261030-10 / R-20261030-01/H17、Status PROVED-LEAN（E464固定族のみ; 最終467jobs/3059decl PASS）。
- New mechanism: E389既知seed w0=S5 A3 S4 A4 S A3の後のSv ATについて、全v>=1/全Tのlocal供給clockを、w0の全20suffixそれぞれのkey二次方程式で分類できるか。自由tagなし、old supplyは別保持。H15 random/H16有限範囲を延長せず、sourceごとの根の全量化子を先に固定する。
- Paper chain: seed suffix zのc=massz/k=runKeyz、先行S gapvを通る供給は i=1-c+v、keyz+4vc-2v²=-2。従って(v-c)²=c²+(keyz+2)/2。固定20suffixから有限根を解析的に得る。Sv内源はclock2のみ。old源はBlockWord key/lowmassから別監査、local分類をactual全供給と同一視しない。
- 最初の紙上old検査: oldC=v+1-i、seedmass0/area=-62/key=-124からoldkey=122-(40+4v)C+2v²。oldkey>=-2でi<=3ならv<=4、C<=2を既存BlockWord mass1/2分類へ落とせる。i4/v6/C3/area7は可能なのでclock4を黙って切らない。これは小定数修理ではなく明示source分類。
- Acceptance: 全v/i local分類と、その後のactual old供給を含むcharge<=3への真の追加edge、または正確な反例。有限seed範囲のpassはCOMPUTEDのみ。15分でsource根/strict除外が出なければSTOP、同じsolver/大表へ資源追加なし。固定seedの結果を四run全域にしない。
- 最後の追加数学CPU: 現在2.962162秒。single worker1件OS1CPU/wall3/自発0.7CPU、総実測4CPU以内を維持。20suffixの代数根をcertificate生成し、別実装のliteral backward windowでv17..32/i0..64の未使用gap域をholdoutする。discovery root生成は全vの代数候補を出すので、literal checkerは独立検査であり全v不在の証明や完全独立dataとは呼ばない。source/argv/revision/hashを先にfreeze。これ以降当日CPU探索追加なし。

## H18-H20 全長chain（07:25個別kernel確認）

20suffixの全v/i rootsは(v4,i3)/(v8,i5)だけ、Sv源clock2を加えたlocal分類をLeanで全量化。有限計算結果のまま無限域へ外挿していない。old源は同じBlockWord suffixのkey/低mass分類でmass>=3、clock>=4を証明し、local/oldを両方保持する。local<=2/2local<=T、old高々1かつ4以降なので最後rayのcharge<=1。元0実EndN/countへ接続、seed実free>=4は既存r3全長count定理から内部供給し、四run固定seed全体charge<=3を得た。元prefix/seed/全positive/全v>=1/全Tの同じfを保持。

これは全四runcharge候補H15を証明したものではなく、固定seed subfamilyだけ。次のH21は同じ最終S-source+old targetのE457全A>=2R+2と結び、固定seed subfamilyのfull-tail free-gapを閉じる。結論/仮想freeを入力しない。15分/07:45期限で止め、成功前に昇格しない。追加探索CPUなし（当日数学実測3.008169CPU秒、残りを使うための計算はしない）。

07:27:18: 元Intp/padded/zero-fullpositive/shared P2から固定族free-gapまで個別kernel確認。全長local roots→old>=4→last charge1→seed free>=4→total charge3→A>=2R+2→free>=R。新規source4ファイルlint通過。一般H15 charge3とH01は依然CONJECTURED。
