# H-20261104-07: mass2 / no-oldの全separator band-source課金

Owner Codex。Parent R-20261104-01。Status CONJECTURED、work active。探索CPU0、最初20分gate。

Exact: 同元Intp/padded BlockWord/zero-fullpositive/正三run zerohead/同old targetmass2/全v>=1/最後rayに全old供給がない明示枝で元fullgapを供給できるか。全履歴/run長を保持しheadfreeやcount予算を入力しない。

Paper: H06の任意v counter R5/M<=R+1/T=v+j-1を利用。band clock i>=v-1ではE519のstrict cutにより第一A以前を排除し、middleSもdelay0/T=i+j/M=R+1だけでH05のmass2 bridge矛盾が排除する。最初v-1個clockは全sourceを保持して合算、以後は第二A以後local3、元actual last<=v+2。counterの同partitionでheadfree r<=3。generic last<=6(no-old)も保持してr+v<=7。既存r3 A上界からS<=2r+1、正三runでS>=3なのでr1..3。R5と同targetkeyの二次上界から全r1/2/3がprimitive key>=-2に矛盾する。有限history/tableではなく全長symbolic budget。

Falsifier: v1の例外clock数0、v2は1で既存結果と整合。vを最初から有限に切らずactual counterからr+v<=7を供給する。no-oldを勝手に全四runへ一般化しない。EndN baseのsuffix比較は限定bandの必要式として証明し、全futureをresetしない。K>=0は正整数積から内部供給。未知Prop/free結論なし。

受入: 全band-source削減→元last<=v+2→全v actual no-old gap。数学修理1回、Lean-j1-M512/per-process10CPU/wall20、source hash/argvを保存。新edgeなし又はcapならSTOPPEDしC2v3/4 old-D3機構へ切替。旧H13/table再開なし。

## 当日最終判断（2026-11-04）

PROVED-LEAN E543。mass2全v/no-old fullgap。
完全な実時計・commands・失敗receipt・次の入口は[DAILY](RESEARCH_HANDOFF_2026-11-04_DAILY.md)と当日packetを参照。
