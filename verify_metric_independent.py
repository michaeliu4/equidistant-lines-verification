"""Independent exact elementary convexity-certificate audit.
Only the five labels per witness are trusted as candidate pointers.
No certificate generator or generalized mixed-sheet identity is imported.
"""
import json,itertools,collections
from pathlib import Path

def require(condition, message):
 if not condition:
  raise ValueError(message)

HERE=Path(__file__).resolve().parent/'generated'
certs=json.loads((HERE/'data/certificates.json').read_text());base=[]
lex=list(itertools.combinations(range(8),3));edges=list(itertools.combinations(range(8),2))
for record in json.loads((HERE/'data/matching_pairs.json').read_text())['representatives']:
 for raw in record['epsilon_masks']:
  ep=dict(zip(edges,[1-2*((raw>>j)&1)for j in range(28)]));sw=[1]+[ep[0,j]for j in range(1,8)]
  mask=sum((ep[a,b]*sw[a]*sw[b]<0)<<j for j,(a,b)in enumerate(itertools.combinations(range(1,8),2)))
  chi=[q*sw[a]*sw[b]*sw[c]for q,(a,b,c)in zip(record['chi'],lex)]
  base.append({'catalog_index':record['catalog_index'],'mask':mask,'chi':chi})
key=lambda r:(r['catalog_index'],r['mask'],tuple(r['chi']))
require(collections.Counter(map(key,base))==collections.Counter(map(key,certs)), 'Verification failed: collections.Counter(map(key,base))==collections.Counter(map(key,certs))')
triples=list(itertools.combinations(range(8),3))
def derive(n,E,chi,b0,b1,i,j,k):
 sw={v:1 if v==b0 else E[b0][v]for v in range(n)}
 def ep(a,b):return E[a][b]*sw[a]*sw[b]
 def ch(a,b,c):
  t=(a,b,c);sg=(-1)**sum(t[l]>t[m]for l in range(3)for m in range(l+1,3))
  return sg*chi[tuple(sorted(t))]*sw[a]*sw[b]*sw[c]
 h={v:ch(b0,b1,v)for v in[i,j,k]};H={v:-h[v]*ep(b1,v)for v in[i,j,k]}
 def d(a,b):return h[a]*h[b]*ch(b0,a,b)
 def D(a,b):return h[a]*h[b]*ch(b1,a,b)
 def w(a,b):return -h[a]*h[b]*ep(a,b)*d(a,b)*D(a,b)
 return h,H,d,D,w
results=[]
for r in certs:
 E=[[1]*8 for _ in range(8)]
 for bit,(a,b)in enumerate(itertools.combinations(range(1,8),2)):E[a][b]=E[b][a]=1-2*((r['mask']>>bit)&1)
 chi=dict(zip(triples,r['chi']));require(len(r['certificates'])>=1, "Verification failed: len(r['certificates'])>=1")
 for c in r['certificates']:
  b0,b1=c['base'];i=c['anchor'];j,k=c['other'];require(len({b0,b1,i,j,k})==5, 'Verification failed: len({b0,b1,i,j,k})==5')
  h,H,d,D,w=derive(8,E,chi,b0,b1,i,j,k)
  require(len(set(h.values()))==len(set(H.values()))==1, 'Verification failed: len(set(h.values()))==len(set(H.values()))==1')
  sh=h[i]*d(j,k);sH=H[i]*D(j,k);require(sh==sH, 'Verification failed: sh==sH')
  wij,wik=w(i,j),w(i,k);require(wij==-wik and sh==-wik, 'Verification failed: wij==-wik and sh==-wik')
  require(c['h_sheets']==[h[a]for a in[i,j,k]] and c['H_sheets']==[H[a]for a in[i,j,k]], "Verification failed: c['h_sheets']==[h[a]for a in[i,j,k]] and c['H_sheets']==[H[a]for a in[i,j,k]]")
  require(c['a_diff_signs']==[d(a,b)for a,b in[(i,j),(i,k),(j,k)]], "Verification failed: c['a_diff_signs']==[d(a,b)for a,b in[(i,j),(i,k),(j,k)]]")
  require(c['A_diff_signs']==[D(a,b)for a,b in[(i,j),(i,k),(j,k)]], "Verification failed: c['A_diff_signs']==[D(a,b)for a,b in[(i,j),(i,k),(j,k)]]")
  require(c['secant_difference_sign']==sh and c['w_signs']==[wij,wik], "Verification failed: c['secant_difference_sign']==sh and c['w_signs']==[wij,wik]")
 results.append({'catalog_index':r['catalog_index'],'mask':r['mask'],'base':[b0,b1],'anchor':i,'others':[j,k],'verified':'EXACT_SAME_SHEET_CONVEXITY_CONTRADICTION'})
out={'covered_catalogue_pairs':len(results),'all_input_pairs_covered_exactly':True,'depends_on':'Published135-class uniform rank3 catalogue plus separately checked exhaustive matching cover','uses_mixed_sheet_identity':False,'uses_metric_cutoffs':False,'uses_numerical_optimization':False,'certificates':results}
# The primary verifier checks finite-domain coverage separately.
print(json.dumps({k:v for k,v in out.items()if k!='certificates'},indent=2))
