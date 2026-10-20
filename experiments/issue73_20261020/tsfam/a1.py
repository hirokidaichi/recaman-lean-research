from ld import *
mn,mn1=load(sys.argv[1])
for last in (1,0):
  print("last=",'A' if last else 'S', "single states min d (rows D, cols Q=-12..8)")
  print("     "+"".join("%3d"%q for q in range(-12,9)))
  for D in range(-3,7):
    print("D=%2d "%D+"".join("%3s"%(mn1(last,sid(D,Q)) if mn1(last,sid(D,Q))<9 else '.') for Q in range(-12,9)))
