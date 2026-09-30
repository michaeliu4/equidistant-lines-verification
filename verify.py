"""Portable integer-only proof replay. Python 3 standard library only.
The only non-computational dependencies are the analytic geometry lemma
and completeness of the published 135-class oriented-matroid catalogue.
"""
import itertools,json,hashlib,time
from pathlib import Path

def require(condition, message):
 if not condition:
  raise ValueError(message)

H=Path(__file__).resolve().parent/'generated'
pairs=list(itertools.combinations(range(8),2));triples=list(itertools.combinations(range(8),3));colex=sorted(triples,key=lambda x:x[::-1]);pv={e:k+1 for k,e in enumerate(pairs)}

def replay(clauses,tree):
 C=[]
 for cl in clauses:
  p=sum(1<<(x-1)for x in cl if x>0);n=sum(1<<(-x-1)for x in cl if x<0);require(not p&n, 'Verification failed: not p&n');C.append((p,n))
 off=0;leaves=0
 def visit(y,n):
  nonlocal off,leaves
  conflict=False
  while not conflict:
   old=y|n
   for p,q in C:
    if p&y or q&n:continue
    a=(p|q)&~(y|n)
    if not a:conflict=True;break
    if a&(a-1)==0:
     if p&a:y|=a
     else:n|=a
   if old==y|n:break
  require(off<len(tree), 'Verification failed: off<len(tree)');v=tree[off];off+=1;v=v if v<128 else v-256
  if not v:require(conflict, 'Verification failed: conflict');leaves+=1;return
  require(not conflict and 1<=abs(v)<=28, 'Verification failed: not conflict and 1<=abs(v)<=28')
  b=1<<(abs(v)-1);require(not (y|n)&b, 'Verification failed: not (y|n)&b')
  if v>0:visit(y|b,n);visit(y,n|b)
  else:visit(y,n|b);visit(y|b,n)
 visit(0,0);require(off==len(tree), 'Verification failed: off==len(tree)')
 return leaves

def matching_clauses(chi,solutions):
 C=[]
 for quad in itertools.combinations(range(8),4):
  aa={v:(-1)**j*chi[tuple(w for w in quad if w!=v)]for j,v in enumerate(quad)}
  ed=list(itertools.combinations(quad,2))
  for signs in itertools.product([-1,1],repeat=6):
   if any(max(sum(s==color and v in e for s,e in zip(signs,ed))for v in quad)<=1 for color in[-1,1]):
    C.append(tuple(pv[e]*s*aa[e[0]]*aa[e[1]]for e,s in zip(ed,signs)))
 C.append((-1,))
 for mask in solutions:C.append(tuple(-(j+1)if mask&(1<<j)else j+1 for j in range(28)))
 return C

def verify_metric(rec):
 chi=dict(zip(triples,rec['chi']));E={(a,b):1 for a in range(8)for b in range(8)if a!=b}
 for j,(a,b)in enumerate(itertools.combinations(range(1,8),2)):E[a,b]=E[b,a]=1-2*((rec['mask']>>j)&1)
 def ch(a,b,c):
  v=[a,b,c];return chi[tuple(sorted(v))]*(-1)**sum(v[x]>v[y]for x in range(3)for y in range(x+1,3))
 require(len(rec['certificates'])==1, "Verification failed: len(rec['certificates'])==1");c=rec['certificates'][0];r,s=c['base'];i=c['anchor'];j,k=c['other'];require(len({r,s,i,j,k})==5, 'Verification failed: len({r,s,i,j,k})==5')
 h=lambda v:E[r,s]*E[r,v]*ch(r,s,v)
 H=lambda v:-E[s,v]*ch(r,s,v)
 a=lambda v,w:ch(r,s,v)*ch(r,s,w)*ch(r,v,w)
 A=lambda v,w:E[r,s]*ch(r,s,v)*ch(r,s,w)*ch(s,v,w)
 w=lambda v,z:-E[r,s]*E[v,z]*ch(r,s,v)*ch(r,s,z)*ch(r,v,z)*ch(s,v,z)
 require(h(i)==h(j)==h(k) and H(i)==H(j)==H(k), 'Verification failed: h(i)==h(j)==h(k) and H(i)==H(j)==H(k)')
 require(h(i)*a(j,k)==H(i)*A(j,k)==w(i,j)==-w(i,k), 'Verification failed: h(i)*a(j,k)==H(i)*A(j,k)==w(i,j)==-w(i,k)')

start=time.time();catalog=json.load(open(H/'data/catalogue.json'));matches=json.load(open(H/'data/matching_pairs.json'))['representatives'];certs=json.load(open(H/'data/certificates.json'))
require(len(catalog['representatives'])==len(matches)==135, "Verification failed: len(catalog['representatives'])==len(matches)==135")
provided={(x['catalog_index'],x['mask'],tuple(x['chi']))for x in certs};require(len(provided)==len(certs)==1027, 'Verification failed: len(provided)==len(certs)==1027')
covered=set();leaves=0
for q,record in zip(catalog['representatives'],matches):
 require(q['index']==record['catalog_index'], "Verification failed: q['index']==record['catalog_index']");chi=dict(zip(colex,[1 if c=='+'else-1 for c in q['revlex_chirotope']]))
 require(record['chi']==[chi[t]for t in triples], "Verification failed: record['chi']==[chi[t]for t in triples]")
 raw=record['epsilon_masks'];require(len(raw)==len(set(raw))==record['epsilon_count'], "Verification failed: len(raw)==len(set(raw))==record['epsilon_count']")
 for mask in raw:
  require(mask&1==0, 'Verification failed: mask&1==0')
  E={e:1-2*((mask>>j)&1)for j,e in enumerate(pairs)}
  for quad in itertools.combinations(range(8),4):
   aa={v:(-1)**j*chi[tuple(w for w in quad if w!=v)]for j,v in enumerate(quad)}
   colors={e:E[e]*aa[e[0]]*aa[e[1]]for e in itertools.combinations(quad,2)}
   for color in[-1,1]:require(any(sum(c==color and v in e for e,c in colors.items())>=2 for v in quad), 'Verification failed: any(sum(c==color and v in e for e,c in colors.items())>=2 for v in quad)')
  sw={0:1,**{v:E[0,v]for v in range(1,8)}}
  nm=sum((E[e]*sw[e[0]]*sw[e[1]]<0)<<j for j,e in enumerate(itertools.combinations(range(1,8),2)))
  nc=tuple(chi[t]*sw[t[0]]*sw[t[1]]*sw[t[2]]for t in triples)
  covered.add((q['index'],nm,nc))
 tree=(H/f"proofs/chi_{q['index']:03d}.tree").read_bytes();leaves+=replay(matching_clauses(chi,raw),tree)
require(covered==provided, 'Verification failed: covered==provided')
for c in certs:verify_metric(c)
print(json.dumps({'result':'PASS','catalogue_classes':135,'exhaustion_trees':135,'exhaustion_leaves':leaves,'exact_metric_certificates':1027,'seconds':round(time.time()-start,3),'external_dependency':'Completeness of the published Finschi-Fukuda uniform IC(8,3) catalogue; analytic geometric lemmas in the accompanying text'},indent=2))
