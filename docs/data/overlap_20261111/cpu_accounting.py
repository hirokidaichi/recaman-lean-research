"""Summarize measured worker CPU without estimating unmeasured categories."""
import json
from pathlib import Path
packet=Path(__file__).parent
groups={"individual_lean":[],"full_check":[],"tool_regression":[]}
unknown=[]
for path in sorted(packet.glob("H*-result.json")):
    data=json.loads(path.read_text())
    argv=data.get("argv",[])
    if argv and argv[0]=="lake":
        group="individual_lean"
    elif argv and argv[0]=="./scripts/check.sh":
        group="full_check"
    elif argv==["make","test-tools"]:
        group="tool_regression"
    else:
        unknown.append({"receipt":path.name,"argv":argv})
        continue
    groups[group].append({"receipt":path.name,"exit_code":data.get("exit_code"),
                         "cpu_seconds":data.get("cpu_seconds")})
result={}
for group,entries in groups.items():
    result[group]={"measured_cpu_seconds":sum(x["cpu_seconds"] for x in entries if x["cpu_seconds"] is not None),
                   "unmeasured":[x["receipt"] for x in entries if x["cpu_seconds"] is None],
                   "entries":entries}
guard=json.loads((packet/"GUARD_VALIDATION.json").read_text())["results"]
result["guard_validation"]={"worker_cpu_seconds":sum(x["worker_cpu_seconds"] for x in guard.values()),
                            "controller_cpu_seconds":sum(x["controller_cpu_seconds"] for x in guard.values())}
search=[]
for tag in ("width4-discovery","width4-holdout"):
    data=json.loads((packet/(tag+"-result.json")).read_text())
    search.append({"receipt":tag+"-result.json","worker_cpu_seconds":data.get("worker_cpu_seconds"),
                   "controller_cpu_seconds":data.get("controller_cpu_seconds"),"exit_code":data.get("exit_code")})
result["mathematical_search"]={"worker_cpu_seconds":sum(x["worker_cpu_seconds"] for x in search),
                              "controller_cpu_seconds":sum(x["controller_cpu_seconds"] for x in search),
                              "budget_worker_cpu_seconds":8,"entries":search}
result["unknown_receipts"]=unknown
result["scope"]="Completed wait4 measurements include the completed validation job and reaped descendants. Per-process limits are not a process-tree cumulative cap. Unmeasured lints, registry checks and shell/git CPU are not recorded as zero. Guard, mathematical search, Lean and regression CPU are distinct and are not added to journal wall time."
(packet/"FINAL_CPU_ACCOUNTING.json").write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n")
print(json.dumps({k:{a:b for a,b in v.items() if a not in ("entries",)} for k,v in result.items() if isinstance(v,dict)},ensure_ascii=False))
