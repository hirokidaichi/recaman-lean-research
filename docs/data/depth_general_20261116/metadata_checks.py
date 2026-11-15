from pathlib import Path
import ast,subprocess,json,hashlib
for f in ["finalize_daily.py","publish_daily.py"]:ast.parse(Path(__file__).with_name(f).read_text())
for cmd in [["bash","scripts/check_module_architecture.sh"],["bash","scripts/check_research_registry.sh"],["make","check-manifest"],["git","diff","--check"]]:
 subprocess.run(cmd,check=True)
p=Path(__file__).parent
m=json.loads((p/"FULLCHECK-R-source-tree.json").read_text())
assert all(hashlib.sha256(Path(k).read_bytes()).hexdigest()==v for k,v in m.items())
assert "@@FINAL_WORK@@" in Path("docs/RESEARCH_HANDOFF_2026-11-16_DAILY.md").read_text()
assert "@@PUBLICATION@@" in Path("docs/RESEARCH_HANDOFF_2026-11-16_DAILY.md").read_text()
assert not Path("Recaman/DepthSixSevenSourceReduction.lean").exists()
print("Final metadata/source/registry/manifest checks passed; finalized work not yet claimed.")
