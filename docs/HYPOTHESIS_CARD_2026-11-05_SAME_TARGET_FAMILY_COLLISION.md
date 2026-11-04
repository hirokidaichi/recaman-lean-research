# H-20261105-01: mass1/no-oldの同target source-family衝突

Owner Codex。親R-20261105-01。Status PROVED-LEAN（E557/E558/E559、全check受理、人間レビュー未）、数学探索worker初期予算0。最初15分gate。

## 一問と全量化子

任意e:Int→Bool/元p:Int/任意padded BlockWord prefix w++A^a末尾n、nで元Endable/S同数、n以後gap末尾まで全正prefixで元Endable+1<=S。全h,M,m,L,s,U>=1、S=h+m+s=M+L+U、head S^h A^M S^m A^L S^s A^U、全T/j、後続S^v A^T S^j、全v>=1。同じ元old target t<nのP2、suffix mass1を仮定。元full-tail actual free F<R=j+1という反例に限定する。

最初の対象はv1。第一A family源と第二S family源の二実P2が異なる最後ray clock i,k<Tを供給できないことを、同じtarget/元prefix/それぞれのsource suffix S数から内部供給できるか。old有無を必要以上に仮定しない共同source補題を優先し、その後no-old枝のfullgapへ接着する。全他oldmass/source以前prefixを保持、M/R/headfree/五供給/結論を新Propのhypothesisにしない。

## 既存入力と最弱edge

[11/04 DAILY](RESEARCH_HANDOFF_2026-11-04_DAILY.md)→[family collision note](RESEARCH_NOTE_2026-11-04_C1_FAMILY_COLLISION.md)→本カード。E553は元p counterのheadfree4/v<=2、E556はv1 no-old lastactual5/free=j、E555はmass1 target/d<=2の任意mixed二窓source排除をPROVED-LEANで供給済み。E551 late source i>=v+1排除/E548 AS+2/E549 cross0境界を再証明しない。

E557 PROVED-PAPER（未Lean・人間レビュー未）のnew edgeはv1で別clock0/1の二caseを同target cross式から排除すること。middleS1ならM=R/h=R+1、firstA0のX=R/delta-1でN0に矛盾。firstA1ならM=R+1/h=R+1、middleS0のdepth2、X=R+2でN0に矛盾。各source固有N>=1を同じNと仮定しない。

## 反証・受入・停止

E550 literal h6/M6/w=SAAAAのfirst供給2を再利用し、first supply1への誤消去は禁止。i=v境界を一律消去しない。初期S/第一A/第二S source位置とAS crossの正負を別passで監査する。元target endpoint Aやsource前grammar resetを入力しない。

受入は共同source排除又はそれによるstrict候補削減、続いて元p no-old actual fullgap。clock同値wrapper/既存free=j再掲/合成だけを進捗にしない。個別Lean -j1 -M512/10CPU per-process/20wall、current bytes receipt・G5・Audit・全check必須。per-process capをtree累積と呼ばない。

最初15分で新共同source edge/strict削減/反例がなければ残り45分をv2のinitial0/final2/第一A・第二S<=2のclock衝突25分と、共通prefix/source個別N・count union十分条件20分へ再配分する。v2機構は初期S源を全消去せずclock0へ保持するのでE554 PAPER/H21 STOPPEDを入力しない。07:45探索終了、確定journal stop・検証済みorigin/main publicationを08:00前に完了。

H08/H10/H12/H13/H21の512MB source、旧H13八head/H06/r4二回0/0等はSTOPPED保持。資源追加・tactic/split/import移動だけで再開しない。C2v3/4 old、非zerohead/他target位置/一般run/rank/C1/Q/H/SL/全射性は未解決。

## 2026-11-05 実行結果（途中）

H01 gateは06:06に新joint source edgeで通過。v1全clock衝突/local4、v2 initial0保持/local5、元p/zero-fullpositive/padding/全v no-old fullgapを06:12までに個別-j1 -M512受理、06:14:34にfullcheck744jobs/3560 declarations及びallowed axioms PASS。E557をPROVED-LEAN、E558/E559を新source/count inputとして登録。数学修理/数学workerなし、compilerのcast/append/namespace修正とregistry参照漏れを修正。停止枝再開なし。残る当日枠は独立old/initial joint-key制約と元actual接続の局所探索へ（予定配分変更、実績はjournal）。
