# C1 source族: H16の弱化count例から実freeへ

結論（E-432、PROVED-PAPER、未Lean・人間レビュー未）: 任意の元基点p、任意の実sign列eとpadded BlockWord全prefix [p,p+n)、任意h>=0、R>=5、1<=M<=3について、以後の実tailが

`S^h A^M S^(R+1) A^R S A^(R+1)`

なら、その**元pからEndableでないAの個数は2R-2以上**である。R/語長/old prefix長の上限を置かず、zero/positive不足/次の供給を仮定しない。Nat f/元0版で述べれば、このtailの長さB=h+M+3R+3に対し `cN (fun i => f i=true ∧ ¬EndN f 0 i) n B >= 2R-2`。padded prefixは全体をBlockWord wとして扱える（既存block_append/block_replicate_A）。

この族の後のS-gap j=R-1は、供給の有無によらずj+1=R<=2R-2でfree-gapを満たす。E430の数値tupleの実freeを仮定し直さず、sourceの可用性から実countを導く部分族の結果である。一般三A-run/C1/Q/H/SLやrankを解いたとは主張しない。

## 紙上依存chain

既存E417で第一A-runの最初min(M,2)個は実free。以降二つのA-runで各供給数<=2を示す。各A-runの前には既にR+1>=6個のSがあるから、E411で同じ実old prefixのold供給は全massを合わせて各run内高々1。残るlocal供給は各runでclock i=2だけであることを以下で示す。local/oldの重複を二重に排除せず、和集合上界1+1を使う。

A-only未来の実local P2は、直前prefixのsuffix vについて `mass(v)+i=1` かつ `runKey(v)=-2` を満たす（E408のj0版）。current A-only run内の新しいAだけから始まるsuffixはarea正でP2にならず、既存localSupply_A_S_iffのj0版がこれを除外する。定符号run内のsuffixを全て分類する。q/eは必ず1以上であり、zero長sourceは別run境界として扱う。

### 第二A-run前: S^h A^M S^(R+1)

- 最後S-run内: q個のSのkeyは-2q²。key=-2ならq=1、mass式からi=2。
- A^M内: e個のAとm=R+1個のS。key=-2は `m(m-2e)=1`。m>=6、e<=3なのでm-2eは非負整数。0なら積0、1以上なら積>=6で不可能。
- 最初S内: q個のSを取ると、E409のkey式から `(q+m)²=2Mm+1`。q>=1/M<=3より左辺>=(m+1)²、右辺<=6m+1。差m²-4m=m(m-4)>0（m>=6）で不可能。

よってlocal供給はi=2のみ。旧prefixはE411で高々1なので第二A-runの実供給<=2、実free>=R-2。

### 第三A-run前: S^h A^M S^(R+1) A^R S

5種類のsourceを漏れなく確認する。

- 最後S内: 1個だけなのでkey=-2、i=2のみ。
- 直前A^R内: e>=1個のAの後にS1。key=4e-2は-2にならない。
- 中央S^(R+1)内: q>=1個のSの後にA^R S。key=-2は `(q+1)²=2R+1`、mass式は `i=q+2-R`。i>=0ならq>=R-2。したがって `(R-1)²<=2R+1`、すなわちR(R-4)<=0となりR>=5に矛盾。
- 第一A^M内: e<=3個のAの後にS^(R+1) A^R S。key=-2は `2e(R+2)=R²+2R+3`。R>=6では右辺-6(R+2)=R²-4R-9>0。R5では右辺38に対して左辺は14/28/42で一致しない。E431のsource再使用式からも `2(R+2)(e-1)=R²-1` として同じ制約を得る（targetのd1部分のliteral P2は下記）。
- 最初S内: q>=1個のSを取ると `(q+R+2)²=2M(R+2)+2R+1`。左辺>=(R+3)²、右辺<=8R+13。差R²-2R-4>0（R>=5）で不可能。

よって第三A-runもlocal i=2のみ、全実old供給は高々1なので実供給<=2、free>=R+1-2=R-1。

### 実countへの接着

S-only区間のfreeは0。元pのEndableを全区間で用い、cN/countP加法で第一free>=min(M,2)>=1、第二>=R-2、第三>=R-1を加える。全free>=2R-2。必要なのは各runでの既存のold一意性であり、old sourceがrunを越えて一回しか使えないという未証明の単射は用いない。

## target / countermodelとの関係

`A S^(R+1) A^R S A^(R+1) S^(R-1)` は全R>=1でmass1/area0（mass加法とrunKey加法を展開すれば確認できる）。このd1窓は最初A-runの最後のAを始点にできる。endpoint Aがあれば元pの実Endableを供給する。しかし上のfree下限があるのでR>=5ではC1の反例にならない。
E430のM1/R5/free4という数値例はsource窓そのものは持つが、全old source/全hでもfree>=8が必要で、数値countを実EndNへ持ち上げられない。M2/3の同じskeletonも含む。旧literal h39 replayの実free10/11/12はこの下限と整合するが、有限replayを本紙上全長証明の代替にしない。

## falsifierと境界

- 空hでも第一Aは元BlockWord直後なのでE417を適用できる。M1/2/3の空run扱いを混ぜない。Rは5以上なので第二/第三runは非空。
- R4では中央S由来の第三A-run clock0が実現する: `S² A⁴ S` はmass1/area0。従って『localはi2だけ』のR>=5を落とさない。親free-gapの反例ではない。
- M4/R5では第二A-rayに `S A⁴ S⁶ A⁴` のP2があり、i4の追加local源を許す。M<=3を落とした同じsource分類は偽。
- local i2が実oldと重なる可能性を残す。上界2は重複を許す和集合上界であり、実供給が必ず2あるとは言わない。
- endpointのSはEndableではなく、count区間はtargetを含まない。source keyを満たすだけでendpoint Aを黙って供給しない。

## 最弱の未検査edgeと次回gate

紙上の全source分類をliteral suffix列挙と同じf/元0の実EndNへ移すことが最弱の未Lean edge。次回はまず第二/第三local rayの全長clock一意性を15分gateで供給し、E411のold予算とcN加法へ接着する。新しい自由tagやE430の数値countを入力にしない。
R/Mを有限上限へ切って全長証明を代替しない。15分でsource型の一つも閉じなければ、この形式化unitをSTOPPEDとして、第二S起点targetの平方条件と実freeの新couplingへ切替える。人間レビューは未実施。
