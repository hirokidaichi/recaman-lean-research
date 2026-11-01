import sys
sys.argv=['auto.py']+sys.argv[1:]
import auto
g,good,seen=auto.main()
for s in sorted(good,key=str): print(s)
