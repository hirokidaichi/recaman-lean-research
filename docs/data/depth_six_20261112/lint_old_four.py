import subprocess
modules=['DepthSixOldFour', 'OldFourHighWindowSpectrum', 'OldFourFreeHeight', 'DepthSixFourRefinedWeight', 'OldFourInitialSS', 'OldFourSecondClockBudget', 'OldFourHighFreeZero', 'OldFourGap', 'SevenWindowPrefixFive', 'DepthSixOldSourceGap']
for m in modules:
 subprocess.run(["python3","scripts/harness_gate.py","--lint-module","Recaman/"+m+".lean"],check=True)
