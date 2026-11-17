import sys,time,threading,os
mode=sys.argv[1]
if mode=='normal':print('normal complete',sum(range(10000)))
elif mode=='wall':time.sleep(10)
elif mode=='cpu':
 def spin():
  n=0
  while True:n+=1
 threading.Thread(target=spin,daemon=True).start();spin()
elif mode=='fork':
 try:os.fork()
 except PermissionError as e:print(str(e))
 else:raise AssertionError('fork unexpectedly allowed')
elif mode=='exec':
 try:os.execv('/usr/bin/true',['true'])
 except PermissionError as e:print(str(e))
 else:raise AssertionError('exec unexpectedly allowed')
