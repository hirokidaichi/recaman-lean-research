# Lean validation cost lesson from this run

同じ`second_double_six` signature（frozen sourceで照合）について、六形Orをomegaへ直接渡すlayoutは-M512でkernel memory失敗（CPU2.529650秒/wall2.695164秒）。同じ命題を明示constructorで組み立てたproofは同-M512で成功（CPU0.633095秒/wall0.802824秒）。失敗対成功の一組であり「4倍高速化」の比較実験ではない。上限追加やcompiled import移動ではない。仮定/全量化子/結論を変えず、候補を有限切断したものでもない。

計測の正本はLEAN_VALIDATION_COST.json/各result/log、source bytesはfrozen。汎用の大表/I25 monolithを再開する根拠にはしない。純算術helperは単独研究結果に数えず、同word source/actual coreから使用する。最終通常全checkは差分build543jobs/3163decl、8.221094秒wall（check_0747）。完全cold検証や全module512MBを示すものではない。
