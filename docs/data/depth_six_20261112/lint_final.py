import subprocess
modules=['DepthSixFourLocalSourcePrefix', 'DepthSixLocalPrefixPair', 'FirstSOneFreePrefix', 'DepthSixLocalSourceClock', 'FirstSFourPrefix', 'DepthSixClockFourPrefix', 'DepthSixClockFourHighWindow', 'DepthSixClockFourCollision']
for m in modules:
 subprocess.run(["python3","scripts/harness_gate.py","--lint-module","Recaman/"+m+".lean"],check=True)
