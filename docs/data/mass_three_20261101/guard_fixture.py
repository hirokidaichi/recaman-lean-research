import sys,os,time,threading
mode=sys.argv[1]
if mode=='normal': print('normal completed')
elif mode=='fork':
 try: os.fork()
 except PermissionError: print('fork rejected before child creation')
 else: raise AssertionError('child creation was allowed')
elif mode=='wall': time.sleep(2)
elif mode=='cpu':
 def spin():
  while True: pass
 a=threading.Thread(target=spin);a.start();spin()
