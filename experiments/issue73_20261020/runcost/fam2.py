exec(open('verify.py').read().split('for w in sys.argv')[0])
for k in range(1,8):
  for m in range(max(0,k-2),k+1):
    w="SSAAA"+"SSSAAA"*m+"SSAAA"+"SA"*k+"AA"
    run,out,st=analyze(w)
    if run: print(k,m,len(w),'r=',out[0][0],'slack=',out[0][2], w)
