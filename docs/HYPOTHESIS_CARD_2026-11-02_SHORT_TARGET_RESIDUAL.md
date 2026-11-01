# H-20261102-12: short-target counter の解析的残余band

Status: PROVED-PAPER（末尾の終了時判断を正本とする。以下は開始時の仮説・費用条件）。07:27近傍開始、10分gate07:37。親R-20261102-01。探索CPU追加0。

問い: E520の全量化子を維持し、counterの全C/v/RをC4..8/v1..4/R5..9の明示五bandへ解析的に削減できるか。全old prefix/historyは無制限で、有限history分類/反例不在とは呼ばない。actual last supply<=4（C=v+1）/<=3（C>=v+2）をsource全包含から供給し、既存head supply<=10へ接着する。

受入: 全sourceを網羅しactual countsと同じ元基点を保つ完全紙上chain、境界と代数の別pass監査。Lean未接着部分はPROVED-PAPERのまま。C/R/S/free結論を新しいPropへ仮定化しない。下界R5及びM予算はE520内部供給。五bandはカードを固定した後に証明する。

候補band: (v,C,R)は(3,4,5..8)、(4,5,5)、(1,4..8,5..9)、(2,4..7,5..8)、(3,5,5..6)。後三bandではD=C-v>=2とR²+D²+4Dv+v²+24v<=145を保持する。単なる箱上界だけへ緩めて候補全部を実現可能扱いしない。

反証pass: C=v+1のmiddleS/i0は残す。local thirdA/finalSの共有clock2を二重計上せず、初期/old全除外はE520を使う。S上界は実head供給10+last3/4+free counterの加法から供給し、初期source前のfreeに置換しない。関数S²-2CSの上界への代入はS>2Cを先に証明する。

停止: 07:37に完全chainが得られなければCONJECTURED/STOPPEDを正確に記録して独立監査へ。新しい大表やCPU探索を開始しない。07:45以降は検証/記録/公開のみ。

結果（H12終了時点）: E-521 PROVED-PAPER。完全chainと独立境界監査をRESEARCH_NOTE_2026-11-02_SHORT_TARGET_BAND.mdへ記録。当時はlast actual3/4と五band包含が未Leanだったが、後続H13/E522で元p actual last3/4はPROVED-LEAN。五band包含は未Lean/人間レビュー未を保持。有限history不在を主張せず、旧tableを再開しない。

## 終了時判断

E-521 PROVED-PAPER、人間レビュー未、五band包含未Lean。 全体検証・逐語audit・実績正本は11/02 DAILY/journalを参照。親C1全体は未解決。
