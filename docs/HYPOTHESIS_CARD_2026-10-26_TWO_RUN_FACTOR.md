# Hypothesis card: 二つのA-runの平方因子と初期S長非依存の上界

- ID: H-20261026-03
- Status: PROVED-LEAN
- Parent: R-20261026-01、E408。再配分したmulti-run20分。
- Mode: 局所探索/活用。最初20分で全suffix分類と非h依存上界を供給できなければ、主張を仮定せず未完了/停止を保存。

## 一問・全量化子

任意h,M,m,r,j : Nat、R=j+1とする。
localSupply(S^h A^M S^m A^r S^j)が真となるのは、以下三種類のsuffixのどれかがある場合に限るか。
1. 最後のS-run内: r=2R、R≤m。
2. 最初のA-run内: ∃a,1≤a≤M、r+a=R+m、R²=m(m−2a)（Int等式）。
3. 最初のS-run内: ∃q,1≤q≤h、M+r=R+q+m、R²=(q+m)²−2mM（Int等式）。
全r/jを量化する。M,m>=1なら真の供給に対し **r≤max(2m,M(m−1))** を導けるか。
初期hや総語長の上限なし。M0/m0はこの上界から外し、全suffix同値自体では落とさない。

## 紙上chain・最弱edge

E408をu=S^h A^M S^mへ適用し、dropの始点を三runへ分解。
P(S^q A^M S^m)=4mM−2(q+m)²、P(A^a S^m)=4ma−2m²、P(S^s)=-2s²。
3ではE=M+r=L+R、D=L−R、DE=2mM。M,m>=1ならD>=1、D=1は偶奇で不可能なのでD>=2。
従ってE<=mM、r<=M(m−1)。2はR<mかつa>=1よりr<=2m−2。1はr<=2m。
最弱edgeは三種類が全suffixを含むことと、同じsuffixのmass/key両条件を同時に保持すること。

## 反証・sharp family

空run/h0、r0、j0、M0/m0で攻撃し、条件外を黙って切らない。
M4、m>=2、h>=m+1、r=4(m−1)、j=2m−2は3のq=m+1で供給され、crossing上界を達成するはず。
m>=3ではr>2mとなるので、最初のA-runを無視する強いr<=2m案への反例族。
親C1/Qや一般free-gapの反例とは呼ばない。語長/rの延長探索ではなく、新平方因子機構のパラメータ攻撃。

## 受入・停止・費用

全suffix双方向同値/明示上界/等号族を一般Leanで確認し、実全history EndN（元0/p）へ接続。
候補存在や平方因子条件を仮定しただけの上界は未解決扱い。G5/Audit/全体check前は昇格しない。
CPUは実行前protocolでfreezeしsingle-worker契約/正確wait4、discoveryと独立holdout、source hash/argv/出力を保存。
20分以内の新edgeがあれば次の未知edgeへ配分し、同じ停滞で上限を増やさない。数学的修理1回まで。
7:45新数学停止/8:00保存終了、親/子/並行CPUの二重計上なし。

## 判定

E-409。全suffix三分類・初期h非依存上界・M4無制限sharp族・実元0/Int元p adapterが個別Lean/lint、全体check414jobs/2825公理監査に成功。
21,600 discovery/384独立holdoutと長いsharp対照に違反0。M0/m0では上界が破れるので条件を残す。
数学的な修理なし。tacticの推論/代数正規化の失敗log/sourceを保存。L/rは第2A-runの長さで、free個数ではない。
全history形を仮定する実adapterを、任意padded prefix後のlocal tailだけへ適用しない。人間レビュー未。
次は同じprefix内の各定符号runからの供給候補が高々1であることを使い、供給A個数をrun数で払う入力。

## 当日journal確定実績
親cycle R-20261026-01: 06:02:22.120877〜07:59:56.352321、確認済み117分34.231秒、不足2分25.769秒。
このcardは同じcycleの一部で、別cycle/CPUとして追加加算しない。unit別実績/commands/再配分/失敗/残課題は[当日DAILY](RESEARCH_HANDOFF_2026-10-26_DAILY.md)と[journal](data/daily_research/2026-10-26.json)を参照。待機/未確認/前日分の加算なし。
