E551のsource i>=v+1除去・actual last v+4・headfree4と原p adapterは07:23:29個別M512受理、E552のr4又はS7/v2/R5/K5 strict残余も07:25:40受理。現在のE551/E552はPROVED-LEAN（人間レビュー未）。以下は先行紙上chainを記録として保持する。

# 2026-11-04: mass1/no-old bandのsource合流

PROVED-PAPER、未Lean・人間レビュー未。共通領域は[同日mass1 note](RESEARCH_NOTE_2026-11-04_C1_MASS_ONE_PAPER.md)の正三run zerohead/同mass1 old target/元Intp/padded/zero-fullpositive、全v>=1でF<Rのactual counter。最後A-ray全old source無しを明示する。R>=5/T=v+R-1/M<=R+1は元actual counterからE545のMassOneTargetCounterが内部供給する。結論やheadfreeを追加仮定にしない。

clock i>=vではdelay=i+j-T=i-v>=0。第二A-run開始より前のlocal source zを取る。target suffixは同prefixのA/key0、source以前のtail prefixをbとする。

1. sourceが初期S又は第一Aの中ならb=S^a A^q（初期Sではq0）。q<=M-1<=R、source以後に最終v>=1個Sが残る。E549へq<=R+1を供給しq=R/a=R+1/delay0。初期Sはq0なので排除。第一Aではh=R+1、q=R、M=R+1、z=n+2R+1、i=vのみ。
2. sourceが第二S内ならb=S^h A^M S^d、0<=d<m。d>=1ならliteral AS pairが存在しE548からM>=R+delay+2となるがM<=R+1に矛盾。d0ならE549からM=R/h=R+1/delay0、同じz=n+2R+1/i=v。

従って二種類のrun位置は一clock i=vへ合流する。他のband源は第二A開始以後であり、そこからのliteral suffixはA^L S^s A^U S^v。定符号A源1とtwo-run2を合わせlocal clock数<=3。早いi<vは全sourceを保持しv時計として合算する。no-old仮定を使って元EndNの全sourceをlocalへ移せば、lastactual<=v+1+3=v+4。T=v+R-1と同じ元count分割、F<Rからheadfree<=4。既存generic no-old last<=6からheadfree+v<=6も保持する。

このheadfree<=4は新しいstrict候補削減であり、C1/no-old fullgapや反例不在ではない。特にr4ならv<=2、r<=3でも残りは未排除。全old履歴は無限のまま。AS+2をfreeへ置換しない。

Falsifierが一回修理: h=R+1だからfirstactual<=1としてfirstA例外を消す案は誤り。R5/h6/M6/w=SAAAAのliteral第一ray供給2（clock2/4）をLean確認したE550。long-first theoremは2M<=h+3を必要とし、この例で失敗する。例外を保持して一clockへ合流する上記証明はこの誤消去を使わない。補助反例は親C1反例ではない。
