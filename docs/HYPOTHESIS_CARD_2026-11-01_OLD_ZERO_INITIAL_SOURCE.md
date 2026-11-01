# H-20261101-06: oldclock0と初期S源の全長非共存

Status PROVED-LEAN E490、親R-20261101-01、活用。任意BlockWord oldsuffix u、任意head z=S^h++x/mass0/cntF>=1、任意v>=1、同じu++z++S^vがclock0のP2である場合、その後の任意Aclock iに初期S開始local sourceが存在しないか。全h/x/v/iを量化、target/free/counter/head長上限を入力しない。

証明chain: 源qでd=h-q、localmassからd+i=v+1。oldmassはD=v+1。共通headをS^d++(S^q++x)に分解しkeyを引き算するとkey(u)=-4i(S+v)-2d²。i0ならd>=2、i>=1ならS+v>=2、従ってkey(u)<=-8。しかしBlockWord key>=-2で矛盾。最弱edgeはこのsource非共存、語の面積や独立old tagを仮定しない。

反証pass: BlockWordを外すとu=SSAAAA、z=SSSSAAAA、v1/i0で同old0と初期S源q2が共存（massu2/keyu-8）。親C1反例ではない。E480はoldclock1なので非共存主張と整合。

受入: 無制限word-source不等式のLean、次にforwardheadfree E489とlast countを実元pへ接着。初回15分で非同値edgeなしならC4 bootstrap PAPER監査へ切替。新CPU0、必要な固定weakword監査だけ事前許可。修理一回、10CPU/20wall/-M512。停止LargeOldSeedGapへ資源/compiled分割だけで戻らない。H06はtarget/free反例を仮定しない別のsource不等式。

最終実績は当日DAILY/journal参照。親R-20261101-01内のunit区間だけを計上し、カードごとに親費用を重ねて加算しない。
