"""Reproducible read-back of adopted module bytes and verbatim signatures."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0,"scripts")
import harness_gate

packet=Path(__file__).parent
rows=[row for row in harness_gate.read_registry("docs/EVIDENCE_REGISTRY.tsv") if 647<=int(row[0][2:])<=677]
modules=sorted({row[4] for row in rows if row[4].endswith(".lean")})
receipts=[(p,json.loads(p.read_text())) for p in packet.glob("H*-result.json")]
module_results=[]
for module in modules:
    digest=hashlib.sha256(Path(module).read_bytes()).hexdigest()
    matches=[str(path) for path,data in receipts if data.get("exit_code")==0 and
             "-M512" in data.get("argv",[]) and
             data.get("source_sha256",{}).get(module)==digest]
    assert matches, (module,"current adopted bytes lack a successful 512MB receipt")
    result=subprocess.run(["python3","scripts/harness_gate.py","--lint-module",module],
                          text=True,capture_output=True)
    assert result.returncode==0, (module,result.stdout,result.stderr)
    module_results.append({"module":module,"sha256":digest,"matching_512MB_receipts":matches,
                           "lint_exit":result.returncode,"lint_output":result.stdout})
(packet/"FINAL_LINT_AND_CURRENT_BYTES.json").write_text(json.dumps(module_results,ensure_ascii=False,indent=2)+"\n")
index=harness_gate.theorem_index()
statements=[]
for eid,label,_,_,artifact,symbols,_ in rows:
    if label!="PROVED-LEAN":
        continue
    text=Path(f"docs/statement_audits/{eid}.md").read_text()
    names=symbols.split(";")
    errors=harness_gate.statement_audit_errors(text,names,index)
    assert not errors,(eid,errors)
    for symbol in names:
        _,signature,proof=index[symbol]
        statements.append({"id":eid,"symbol":symbol,"verbatim":True,
            "signature_sha256":hashlib.sha256(harness_gate.signature_text(signature).encode()).hexdigest(),
            "proof_kind":harness_gate.proof_kind(proof)})
(packet/"FINAL_VERBATIM_SIGNATURE_AUDIT.json").write_text(json.dumps(statements,ensure_ascii=False,indent=2)+"\n")
print(json.dumps({"modules":len(module_results),"signatures":len(statements),"all_current_512MB":True,"all_verbatim":True}))
