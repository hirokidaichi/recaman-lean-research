# 2026-10-31: 全長moment帯の四run free-gapと帯外source対

結論: E482 PROVED-LEANは、任意元Intp/padded BlockWord履歴/zero-fullpositive、正三A-run head `S^h A^M S^m A^L S^s A^U` で `M+L+U=h+m+s=S`、area=-B、`4S+4<=B<=6S+4`、同じold targetと最終S local bandに限り、第四A-run後のS-gap jに `j+1<=実full-tail free` を供給する。全S/head長/old履歴/未来長に上限を入力しない。全四run/C1/任意r rank/全射性は未解決。既存kernel r3 countに依存し未検証r4 table/E384存在方向に依存しない。人間レビュー未。

## 完了した依存chain

1. E467〜469: 初日のS10二caseを元counterから内部供給し、local4/5とheadfree4を実countに接着。
2. E470/471: 任意Sの同じtargetはmass<=2/v<=3。全old-last排除と必要反例域S<=16を供給。
3. E472〜475: source族を同じwordで分解し、重複clock0/2を一度だけ数える。mass1 targetの全Sを完了。S7は表を捨てheight不等式で解いた。
4. E476〜478: mass2反例はj4/fullfree4/九parameter群。last local3/4/5でlastfree>=1、headfree4と矛盾し元帯4S+6の全Sを完了。
5. E479〜482: lower5のAA例外は同じtargetとarea偶奇で消える。さらにlower5のR>=5 counter target自体が実語では空と監査したため、形式的な下端拡張を新履歴coverageと数えない。実在するlower4境界ではold供給を切らず高々1とし、target A/v2/S>=16を内部供給。local<=5/head実供給<=10/headfree>=6でfull freeを払った。

E480 REFUTEDはlower4までのold-erasure補助案の反例。old SAAA/S6又はS16の元0zero/fullpositive履歴でclock1 oldとtarget/localが共存する。fullfreeは十分なのでC1反例ではない。E482はこの実在領域も含む。

## 帯外mass3 target/source4の紙上縮約（E483候補）

この節の水準はPROVED-PAPER（未Lean・人間レビュー未）。actual free-gapの結論ではない。
任意同じBlockWord wの二suffixをx=w.drop s（mass4）、y=w.drop t（mass3）とし、任意zero-mass head zのS=cntF z、area=-Bを固定する。最終S長を3、xが最後Aのclock0を供給し、yが同じheadの後の A^T S^j targetを供給する。全S/j/head/元prefix長を量化する。R=j+1。

E394のmass3語はAAA/SAAAA/ASAAA、area6/5/7。E398のmass4六語はAAAA/AASAAA/ASAAAA/SAAAAA/SAAASAAA/SSAAAASAAA、area10/13/11/9/12/9。共通wの二suffixは互いにsuffix比較可能なので、area対(a4,a3)は次の10対だけになる（重複area9/6は一対と数える）。

| a4,a3 | 共通wordの例 | BとSの偶奇 | R²の式 | 判定 |
|---|---|---|---|---|
| 10,6 | AAAA | S偶数 | 2S+7 | 平方mod4=3で排除 |
| 10,5 | SAAAA（x=AAAA） | S偶数 | 2S+8 | 残す |
| 13,7 | AASAAA | S奇数 | 2S+9 | mod4=3で排除 |
| 13,6 | AASAAA | S奇数 | 2S+10 | 残す |
| 11,5 | ASAAAA | S奇数 | 2S+9 | mod4=3で排除 |
| 11,6 | ASAAAA | S奇数 | 2S+8 | mod4=2で排除 |
| 9,6 | SAAAAA又はtrip | S奇数 | 2S+6 | 残す |
| 12,7 | SAAASAAA | S偶数 | 2S+8 | 残す |
| 12,6 | SAAASAAA | S偶数 | 2S+9 | 残す |
| 9,7 | trip | S奇数 | 2S+5 | mod4=3で排除 |

列挙の全包含は六語×三語を両方向suffix比較して得る。target SAAAAがsupplier AAAAを含む場合もあり、元sourceの位置順序は勝手に固定しない。

計算ではなく原始keyを使う。key(x)=2a4−20、key(y)=2a3−12、key(z)=−2B。clock0 sourceの同じkey式は
`key(x)+key(z)+16S+48−18=-2`、従って `B=8S+a4+6`。
同じtargetは `key(y)+key(z)+12S+36−18=-2R²`、従って
`R²=2S+3+a4−a3`。
任意zero-mass wordでは `B≡S (mod2)`（任意語の二倍area帰納式とlength=2Sから）。ゆえにS≡a4 (mod2)。表の五対は平方mod4が2又は3となるため不可能。残る五対は
`(10,5),(13,6),(9,6),(12,7),(12,6)`。

この縮約は同じtarget/old sourceのcouplingを使うstrict pair削減であり、各massを独立選択しただけでは得られない。ただし残る五対が実positive履歴で実現可能か、actual free/countを払うかは未証明。v4/oldmass5も未処理。他supplierの高massや源以前のprefixを全historyから切った主張ではない。

形式化layoutは一回定数修理の後512MB kernel memoryでSTOPPED。隔離packetの未検証sourceは証拠に使わない。再開には独立した因数化/小さい完全certificateを必要とし、同じ18pair+mod4 layoutへの時間/メモリ追加やcompiled import移動だけでは再開しない。

## 失敗・反証と実績の扱い

- 61head tableとS7五形/30cell layoutは512MB STOP。後者に一度通常buildを上限なしで実行した手順誤りがあり、そのsource/cacheを隔離。採用proofは独立した解析的height pruningで同512MBを改めて通した。
- H19最初のv1有限probeはtarget-circle定数の誤りをWin assertionが検出。結果なし。修理S16 discoveryは74positive/minfree16、fresh S30 holdoutは1CPU SIGXCPUで未完了。延長せず、反例不在として使わない。
- E481の境界拡張はcounter域で空とkernel監査し、進展の数から外した。E482 lower4はliteral positive適用例を持つ。
- 予定120分やCPUを実時計へ加算しない。実績は当日journalのclosed intervalsのみ。

## 保存時の有限監査
07:45:09に凍結済み18word pairの表だけをdirect suffix/逆順prefixと二種類のarea評価で独立検算し、10area対/五残余が一致した。COMPUTED監査であり新しい探索、fresh holdout、kernel証明ではない。preflight/argv/sourcehash/正確出力はpacket `PAPER_AUDIT_PREFLIGHT.json` / `audit-paper-pairs.log`。E483の無制限argumentはPAPERのまま、actualfreeは未接続。

## この進展の大きさと、C1への距離

A-runはAが連続する一つの区間であり、「四run」はAが4個という意味ではない。今回、各runの長さをいくらでも許したまま、供給窓の出発点を分類し、同じclockを複数の供給理由で二重に数えない方法を得た。固定seed/S10だけだった確認を、Sの大きさに上限を設けない一つの四run領域へ広げた点が実質的な進展である。

ただし、その領域には「最初三runのA総数とS総数が同じ」「面積が4S+4から6S+4の帯内」「同じold targetと最後Sのlocal源がある」という条件が残る。全四runのうち何割を覆うか、C1まで何割済んだかは測定も定義もできていない。証明ファイル数や有限probeの件数を達成率にしない。

```text
二A-run全長 free-gap E414
          ↓ 三run全長 E451
          ↓ 四run固定seed E464
          ↓ 今回: zero-mass / moment帯 / 指定source枝の全長 E482
          ⋮ 残る: 帯外・nonzero-mass・他target/local源・四run全体
          ⋮ 残る: 任意run数 / 任意free数での一様な供給rank
          ⋮ 残る: Qの累積面積評価への接続、C1の元の義務
```

この縦並びは対象を広げる研究の方向であって、下側の点線が証明済みの含意であるとは言っていない。一般Qの面積評価とC1への最終接着はまだ完成していない。次のmass3枝は今の帯の外で起きる供給源の再利用を直接調べるために選んだ。最初15分で有効なsource制約が得られなければ、同じ形式化を引き延ばさず別source機構へ切替える。
