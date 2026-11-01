from ld import *
mn,mn1=load(sys.argv[1])
for last in (1,0):
 for D1 in range(1,5):
  print("last=%s  state1=(%d,0); rows D2, cols Q2=-14..0 ; entries min d (.=never at d<=2)"%('AS'[1-last],D1))
  for D2 in range(-2,7):
    print("  D2=%2d "%D2+"".join("%2s"%(mn(last,sid(D1,0),sid(D2,Q)) if mn(last,sid(D1,0),sid(D2,Q))<9 else '.') for Q in range(-14,1)))
