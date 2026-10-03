# Evidence addendum

`worker_report.md` は結果凍結後に変更しない。本 addendum は親の原記録照合で判明した
証拠保存上の限界だけを追記する。

1. v2 の runner wall time として転記した `5.611630` 秒は、tool result の
   `wall_time_seconds=5.611629958` に由来するが、program 自身の raw elapsed
   `5.664199` 秒より短い。異なる時計・丸めの可能性を排除できず、stdout 原文にも
   runner wall は含まれないため、この値は**未確認**として撤回する。v2 について信頼する
   時間記録は raw の program elapsed `5.664199` 秒と、02:17前にprocessが終了した事実だけ。
2. 初回 source は実行前 SHA256
   `ead649739e53ca1d52853cac01f11a47f957b1ee1320469849971a5560cdbac5`
   を記録したが、修正前の実体を別ファイルへ保存する前に一回の repair を適用した。
   現在の source は修正版 SHA256
   `d3fc203ba3c42f24000b15dce119f83d016fd7a6fb6d4aa65039327433475a94` である。
   初回 source を推測復元して証拠扱いせず、**初回 source 実体は未保存**とする。
   初回 raw と repair 差分の説明は残るが、初回を独立再現可能とは主張しない。

これらは `INCOMPLETE` 判定を強めるもので、数学的主張、量化子、範囲、修理回数を変えない。
新しいコード実行や研究修理は行っていない。
