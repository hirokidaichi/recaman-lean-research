# Frozen source evidence

`frozen/` stores exact source bytes by SHA for successful and failed validation jobs. A frozen filename is not an acceptance label. Use TAG-result.json exit_code and CURRENT_BYTE_ACCEPTANCE.json to identify the adopted current bytes. STOPPED attempts are separately named under stopped/ and never imported by Recaman/root/Audit. Packet sources are evidence, not library modules. No placeholder, proof escape, or invented axiom was used.

One original snapshot with significant trailing whitespace is stored losslessly as `.lean.gz`. Decompress with Python gzip.decompress and compare SHA256 to the filename. This preserves the exact failed/accepted source bytes without changing their evidence identity.
