import sympy as sp, json, time
out=[]
for start in [4000,16000,64000,256000]:
 p=int(sp.nextprime(start)); attempts=0
 while True:
  if p%12==7:
   attempts+=1
   sq={y*y%p:y for y in range(p)}
   n=1+sum(1 if (v:=(x*x%p*x+7)%p)==0 else 2 if v in sq else 0 for x in range(p))
   if sp.isprime(n):
    divs=[int(d) for d in sp.divisors(p-1) if d%6==0 and d<=256]
    out.append({'p':p,'n':n,'divisors':divs,'attempts':attempts})
    print(out[-1],flush=True)
    break
  p=int(sp.nextprime(p))
open('/mnt/data/m16_cost_pass/toy_selection.json','w').write(json.dumps(out,indent=2))
