# H-20261106-42 — 第三減算列の対象窓と最後ray

- 状態 CONJECTURED。人間レビュー未。
- 問い。真正四A-runの第三S内から始まる実対象窓について、残りS長 (qle3) または (q+j+1le v) なら元の全tail実free-gapが成立するか。
- 全量化子。元Intp/padded BlockWord/zero/fullpositive、全run長、第三S内の始点と実P2終点、全旧履歴・他供給mass。(q) は実始点から第三S右端までの距離、(v) は最後S長。任意qへの延長は別問。
- 受入。対象窓の (S^q A^U S^v A^T S^j) を同じ実履歴から得て、(R=j+1) とすると (T+U=R+q+v)、((q+v)^2=R^2+2Uv)。実free下限または同じ実候補の厳密削減を検証。(q+Rle v) なら (2v(T-2R)=(v-R)^2-q^2ge0) を使う。
- 反証・停止。(q=1,2,3)、(v<q)、(T=0/1)、負の差 (v+q-U)、時刻0/1を保持。分類の各小条件は記号的に因数化し、大きい有限head表にしない。実countに接続しない場合は未検証枝を隔離し、一般qの源順序だけを残す。数学worker予算0。07:45探索終了。

(Uge2q) なら (R^2le(v-q)^2)。(vge q) は長ray、(v<qle3) なら (Rle2)。(U<2q) なら ((R-|v+q-U|)(R+|v+q-U|)=q^2-(U-q)^2in{1,3,4,5,8,9})。差因子は1..3。残りは (Rle2)、(R=3,Uge4)、または ((q,R,U,v,T)=(3,5,3,4,9))。前二群はheadfree (rle R-1) とr3 (Nle2r+1)。最後の一群はT9/free≤4/供給≤7でr≤2、N≤5・v4の新capで最後供給≤6、r≤1となりU3と矛盾。

## 11/06 結果

カードの限定域は E-588 **PROVED-LEAN**。q<=3 又は q+j+1<=v で元Intp/実P2/実free。広いq3算術がCPU/512MBで停止した後、固定q3の独立因数化により候補T9を分離して実供給上限から排除した。E-587は一般qの対象と同separator源の関係、E-589は残余14及び第二A/第三Sの条件付き排除。q>=4の残余飽和排除E-590は **PROVED-PAPER**。H50/H51の旧接続ソースは一回修正後STOPPED。次は[H-20261107-01](HYPOTHESIS_CARD_2026-11-07_THIRD_S_SATURATION.md)。確定実績は[11/06 DAILY](RESEARCH_HANDOFF_2026-11-06_DAILY.md)。
