from ld import *
mn,mn1=load(sys.argv[1])
for last in (1,0):
  print("TS' pairs last=",'A' if last else 'S')
  for j in range(0,5):
    print(" j=%d: "%j+" ".join("i%d:%s"%(i, mn(last,sid(j+1,0),sid(i+j,-(2*i+1))) if i+j<=DM and 2*i+1<=QM else '-') for i in range(0,6)))
