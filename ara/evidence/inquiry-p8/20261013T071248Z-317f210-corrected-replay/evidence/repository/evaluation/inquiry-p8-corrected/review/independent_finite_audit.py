#!/usr/bin/env python3
"""P8 independent finite-table audit over manually inspected source-byte cases.

The hand annotations below are review judgments. This tool independently
enumerates their finite histories/selections/subsets and checks exact ASTs;
it does not check arbitrary Lara sources or call an inquiry driver.
"""
import sys,json,itertools,hashlib,copy,argparse
from pathlib import Path
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--suite',type=Path,default=Path(__file__).resolve().parents[1])
parser.add_argument('--reviewer',help='independent reviewer identity; required when issuing a review receipt')
parser.add_argument('--out',type=Path,help='write a new review receipt; existing paths are refused')
args=parser.parse_args()
if args.out is not None and not args.reviewer:parser.error('receipt requires an independent reviewer identity')
if args.out is not None and (args.out.exists() or args.out.is_symlink()):
 parser.error('review receipt already exists; audit not started: '+str(args.out))
ROOT=Path(__file__).resolve().parents[3];sys.path.insert(0,str(ROOT/'scripts'))
from evidence_measured import parse,canonical
S=args.suite.resolve();M=json.loads((S/'MANIFEST.json').read_text());evidence=[];legacy_evidence=[];findings=[]
def B(t,n):return next(x for x in t if isinstance(x,list) and x and x[0]==n)
def D(x):
 if x[0]=='string':return x[1]
 if x[0].startswith('integer'):return x
 assert x[0]=='node';a=[];tail=x[2]
 while tail[0]=='cons':a.append(D(tail[1]));tail=tail[2]
 assert tail==['nil'];return [x[1]]+a

def digest(x):return hashlib.sha256(x).hexdigest()
def check(ok,c,msg):
 if not ok:findings.append({'case_id':c,'failure':msg})
def boolwire(x):return 'true' if x else 'false'
J=['published','justified'];F=['published','defeated'];REJ=['source',['source',['structural',['duplicate-leaf-id','seed']]]]
# These manually drawn finite endpoint graphs are declarations inspected from bytes,
# not inferred by a source checker. The consumer edge comes from occurrence propagation.
GRAPHS={
'T01': [(['witness'],[],['witness']),(['witness'],[],['witness'])],
'T02': [(['witness'],[],['witness']),([],[],[])],
'T03': [([],[],[]),(['witness'],[],['witness'])],
'T04': [([],[],[]),([],[],[])],
'T05': [(['witness','attacker'],[['attacker','witness']],['witness']),(['witness','attacker','defender'],[['attacker','witness'],['defender','attacker']],['witness'])],
'T06': [(['witness','consumer','attacker'],[['attacker','witness'],['attacker','consumer']],['witness']),(['witness','consumer','attacker','loop'],[['attacker','witness'],['attacker','consumer'],['loop','loop']],['witness'])],
'T07': [(['witness','consumer','attacker'],[['attacker','witness'],['attacker','consumer']],['witness']),(['witness','consumer','attacker','new-attacker'],[['attacker','witness'],['attacker','consumer'],['new-attacker','witness'],['new-attacker','consumer']],['witness'])],
'T08': [(['witness','consumer','attacker'],[['attacker','witness'],['attacker','consumer']],['witness']),(['attacker','witness','consumer'],[['attacker','witness'],['attacker','consumer']],['witness'])],
}
ENDPOINT_STATUS={'T01':[J,J],'T02':[J,None],'T03':[None,J],'T04':[None,None],'T05':[['evidence-blocked','defeated'],['evidence-blocked','justified']],'T06':[F,F],'T07':[F,F],'T08':[F,F],'T16':[J,J]}
LOCALITY={'T01':True,'T02':False,'T03':False,'T04':False,'T05':False,'T06':True,'T07':False,'T08':True,'T16':True}
def ancestors(edges,support):
 out=set(support)
 while True:
  new=out|{a for a,b in edges if b in out}
  if new==out:return out
  out=new

def endpoint_review(c,seed,t,o):
 values=ENDPOINT_STATUS[seed];changed=values[0]!=values[1];tr=('accepted' if values[0] else 'rejected')+'-to-'+('accepted' if values[1] else 'rejected')
 impact=['impact-result',['transition',tr],[['query-impact',['atom','t'],[values[0]] if values[0] else [],[values[1]] if values[1] else [],boolwire(changed),boolwire(LOCALITY[seed])]], [['atom','t']] if changed else [],[['atom','t']] if not changed and values[0] and values[1] else []]
 expected=[]
 for req in B(t,'requests')[1:]:
  if req[0]=='impact':body=['impact-body',impact]
  else:body=['verification-body',['invalid-certificate',['false-read-evidence']]] if req[1]=='tampered' else ['verification-body',['verified']]
  expected.append(['inquiry-result','1',req[1],body])
 check(expected==o['expected']['results'],c,'exact impact/verification expected AST differs from manual endpoint facts')
 if seed!='T16':
  g=copy.deepcopy(GRAPHS[seed]);level=int(c.rsplit('-',1)[1]) if '-source-declarations-' in c else 0
  for side,(names,edges,supp) in enumerate(g):
   names.extend('p8-inert-'+str(i)+'-root' for i in range(level));ag=o['semantic_specification']['graphs'][side]
   check(names==ag['names'] and edges==ag['edges'] and supp==ag['query_support'],c,'authored endpoint graph differs from independently drawn graph')
   check(ancestors(edges,supp)==set(ag['query_ancestry']),c,'backward ancestry differs')
  if values[0] and values[1]:
   region=ancestors(g[0][1],g[0][2])|ancestors(g[1][1],g[1][2])
   nodechange=set(g[0][0])^set(g[1][0]);edgediff=set(map(tuple,g[0][1]))^set(map(tuple,g[1][1]))
   loc=g[0][2]==g[1][2] and not nodechange&region and not any(b in region for a,b in edgediff)
   check(loc==LOCALITY[seed],c,'independently evaluated locality differs')
  # Sanctioned certificates are data; compare their endpoint and query fields
  # against manually justified acceptance, exact rejection and support identity.
  for req in B(t,'requests')[1:]:
   if req[0]!='verify-impact':continue
   cert=req[4];check(cert[1:3]==req[2:4],c,'certificate source pins differ')
   check(cert[10]==impact[1] and cert[11:14]==impact[2:],c,'certificate partition/status differs from independently expected impact')
   for side,value in enumerate(values):
    report=cert[8+side];check(report[1]==boolwire(value is not None),c,'certificate acceptance differs')
    check(report[2]==([] if value else [REJ]),c,'certificate rejection differs')
    check(report[7]==[[['atom','t'],g[side][2]]],c,'certificate stable support differs')
 evidence.append({'case_id':c,'manual_endpoint_statuses':values,'manual_transition':tr,'manual_changed':changed,'manual_locality':LOCALITY[seed],'exact_expected_ast_equal':expected==o['expected']['results']})

def histories(t,seed):
 if seed not in ['T10','T15']:return [[]],1,[]
 record=B(t[2],'record');events=[x[:3] for x in record[1:] if x[0]=='event']+B(t[2],'universe')[1:]
 mapping={x[1]:x for x in events};order=[(x[1],x[2]) for x in record[1:] if x[0]=='order'];reported={x[1] for x in record[1:] if x[0]=='event'}
 valid=[];compatible=[]
 for n in range(len(events)+1):
  for p in itertools.permutations(mapping,n):
   if 'run' in p and ('commit' not in p or p.index('run')<p.index('commit')):continue
   if any(x in p and ('run' not in p or p.index(x)<p.index('run')) for x in ['success','capture','correct-capture']):continue
   if 'aux-run' in p and ('commit' not in p or p.index('aux-run')<p.index('commit')):continue
   if 'wrong-capture' in p and ('aux-run' not in p or p.index('wrong-capture')<p.index('aux-run')):continue
   valid.append(list(p))
   if reported<=set(p) and all(p.index(a)<p.index(b) for a,b in order):compatible.append([mapping[x] for x in p])
 return compatible,len(valid),valid

def rows_for(t,seed):
 hs,steps,prefixes=histories(t,seed);rows=[]
 for h in hs:
  for choices in itertools.product(*[s[2] for s in B(t,'slots')[1:]]):
   if seed=='T15':
    hn=[e[1] for e in h]
    captures=[e for e in hn if e in ['correct-capture','wrong-capture']]
    if len(captures)!=1 or hn.index(captures[0])<hn.index('aux-run'):continue
   pairs=[(s[1][1],ch[1][1]) for s,ch in zip(B(t,'slots')[1:],choices)]
   sel=dict(pairs)
   status=None if seed=='T09' else (J if sel['0']!='0' and sel['1']!='0' else F) if seed in ['T11','T12'] else J
   audit=(sel['0']=='0') if seed=='T10' else any(e[1]=='correct-capture' for e in h) if seed=='T15' else None
   rows.append({'history':h,'selection':pairs,'choices':choices,'status':status,'rejection':REJ if seed=='T09' else None,'audit':audit})
 return rows,hs,steps,prefixes

def completion(t,row):return ['completion',row['history'],[['selection',s[1],ch] for s,ch in zip(B(t,'slots')[1:],row['choices'])]]
def assignment(r):return [[['slot-id',s],['choice-id',c]] for s,c in r['selection']]
def targetkey(obs):return 'audit' if obs[1][0].startswith('audit') else 'status'
def truth(lit,row):
 k,s,c=lit[1];eq=dict(row['selection']).get(s[1])==c[1];return eq if k=='slot-eq' else not eq

def family_review(c,seed,t,o):
 rows,hs,steps,prefixes=rows_for(t,seed);accepted=[r for r in rows if r['rejection'] is None];counts=list(map(str,[len(rows),len(accepted),len(rows)-len(accepted)]));expected=[];analyses=[]
 catalog=B(t,'assumption-catalog')[1:];distinct=[x for i,x in enumerate(catalog) if x not in catalog[i+1:]]
 for q in B(t,'requests')[1:]:
  k,label=q[:2]
  if k in ['status','audit']:
   valrows=[['family-row' if k=='status' else 'family-audit-row',r['history'],assignment(r),[r['rejection']] if r['rejection'] else [],[] if r['rejection'] else [r[k] if k=='status' else boolwire(r[k])]] for r in rows]
   stable=bool(rows) and all((r['rejection'],r['status'])==(rows[0]['rejection'],rows[0]['status']) for r in rows)
   body=[k+'-body',['family-'+k+'-result',valrows]+counts+[boolwire(stable if k=='status' else False)]] # all admitted coverage is open-world; profile excludes it
  elif k=='stable':
   key=targetkey(q[2]);observations=[r['rejection'] or r[key] for r in rows];whole=bool(rows) and all(x==observations[0] for x in observations);domain=bool(accepted) and all(r[key]==accepted[0][key] for r in accepted)
   body=['stability-body',['stability-result',q[2]]+counts+[boolwire(whole),boolwire(domain)]]
  elif k in ['sensitivity','slots-sensitive']:
   rh=B(q[2],'ref-history')[1];rs=[(x[0][1],x[1][1]) for x in B(q[2],'ref-choices')[1]];ref=next(r for r in rows if r['history']==rh and r['selection']==rs);key=targetkey(q[3])
   val=lambda r:r['rejection'] or r[key]
   differing=[r for r in rows if val(r)!=val(ref)]
   changed=lambda r:[s for s,ch in rs if dict(r['selection'])[s]!=ch]
   flips=[]
   for r in differing:
    if r['history']==rh and changed(r) not in flips:flips.append(changed(r))
   minimum=[f for f in flips if f and not any(set(g)<set(f) for g in flips)]
   realized=[next(r for r in differing if r['history']==rh and changed(r)==f) for f in minimum]
   body=[k+'-body',['sensitivity-result',q[3],completion(t,ref),str(len(rows)),str(len(differing)),[['row',completion(t,r),[['slot-id',s] for s in changed(r)]] for r in differing],[[['slot-id',s] for s in f] for f in minimum],[[[['slot-id',s] for s in f],completion(t,r)] for f,r in zip(minimum,realized)]]]
   analyses.append({'label':label,'all_differing_selections':[r['selection'] for r in differing],'all_nonempty_minima':minimum,'first_realizers':[r['selection'] for r in realized]})
  elif k=='minimal-assumptions':
   key=targetkey(q[2]);desired=q[2][1][2] if key=='status' else True
   subsets=[list(s) for n in range(len(distinct)+1) for s in itertools.combinations(range(len(distinct)),n)]
   restrict=lambda s:[i for i,r in enumerate(rows) if all(truth(distinct[j],r) for j in s)]
   satisfies=lambda s:bool(restrict(s)) and all(rows[i]['rejection'] is None and rows[i][key]==desired for i in restrict(s))
   good=[s for s in subsets if satisfies(s)];minimum=[s for s in good if not any(set(a)<set(s) for a in good)];sets=[]
   for s in minimum:
    dels=[]
    for j in s:
     surviving=restrict([i for i in s if i!=j]);counter=next(i for i in surviving if rows[i]['rejection'] is not None or rows[i][key]!=desired)
     dels.append(['deletion',distinct[j],[completion(t,rows[i]) for i in surviving],[completion(t,rows[counter])]])
    sets.append(['minimal-set',[distinct[i] for i in s],[completion(t,rows[i]) for i in restrict(s)],dels])
   body=['assumptions-body',['assumption-result',q[2],catalog,str(len(rows)),sets]]
   analyses.append({'label':label,'literal_truth_table':[[truth(lit,r) for lit in distinct] for r in rows],'all_catalog_subsets':[{'indices':s,'surviving_rows':restrict(s),'satisfies':satisfies(s)} for s in subsets],'all_minima':minimum})
  expected.append(['inquiry-result','1',label,body])
 check(expected==o['expected']['results'],c,'exact family result AST differs from independent finite enumeration')
 spec=o['semantic_specification'];check(steps==spec['history_search_steps'],c,'independent executable prefix count differs')
 if prefixes:check(set(map(tuple,prefixes))==set(map(tuple,spec['executable_prefix_table'])),c,'exhaustive executable prefix table differs')
 expected_rows=[{'history':r['history'],'choices':[[int(s),int(ch)] for s,ch in r['selection']],'status':r['status'],'rejection':r['rejection'],'audit':r['audit']} for r in rows]
 check(expected_rows==spec['rows'],c,'authored row observations differ from manual finite row annotations')
 evidence.append({'case_id':c,'manually_annotated_rows':expected_rows,'independent_history_search_steps':steps,'independent_compatible_histories':hs,'independent_analyses':analyses,'exact_expected_ast_equal':expected==o['expected']['results']})

def manual_audit_binding_review(c,seed,t,o):
 if seed not in ['T10','T15']:return
 rows,hs,steps,prefixes=rows_for(t,seed);bind=B(t,'bindings');w0=next(v for v in bind[2] if v[1]=='w0');profile=next(q[4] for q in B(t,'requests')[1:] if q[0]=='audit')
 check(bind[1]==[['claim-binding','c0','claim',['atom','t']]],c,'audit claim does not freeze exact formal atom/interpretation')
 check(w0[2]=='c0' and w0[3]==t[3] and w0[4]==['artifact-spec','witness',[],['declared',['interpretation-id','0']]],c,'fixed-witness source or declaration association differs')
 check(w0[5]==['sampling'] and w0[6]==['ledger',['ledger-binding','run0','fam','1',['ledger-fields',['some',['p-value']],['some',['rational',['integer-natural','1'],'40']],['some','1'],['some','fwer']]]],c,'audit ledger/probe differs from manually justified guarantee')
 check(profile==['profile',['hypothetical','observed'] if seed=='T10' else ['observed'],['complete','count-bounded'],['guarantee','fwer','1','20'],['sampling'],['acceptance','grounded-justified']],c,'audit profile differs from manual admissible grades/guarantee')
 record=B(t[2],'record');check(not any(v[0] in ['coverage','admit-coverage'] for v in record[1:]),c,'unexpected coverage admission')
 kinds=B(t,'kind-metadata')[1:];admissions=B(t,'admitted-assumptions')[1:]
 for kind in kinds:
  check(kind[1]==t[3] and kind[3]=='observed',c,'kind metadata pin/grade differs')
  a=next(v for v in admissions if v[1]==kind[4][1]);check(a[2]==t[3] and a[3]==kind[2],c,'reader admission source/key binding differs')
  capture=['event','success',['result','run0','1']] if seed=='T10' else ['event','correct-capture',['result','run0','2']]
  check(a[4:]==[capture,'run0','instrumented-log'],c,'capture exact run/event/authority differs')
 facts=[]
 for r in rows:
  runs=[v for v in r['history'] if v[2][0]=='run'];count=sum(v[2][-1]=='fam' for v in runs);check(count==1,c,'common ledger family count changed')
  check(['event','success',['result','run0','1']] in r['history'],c,'ledger result is absent')
  if seed=='T15':check(next(v for v in runs if v[2][1]=='aux')[2][-1]=='other-family',c,'auxiliary run enters common family')
  facts.append({'history_event_ids':[v[1] for v in r['history']],'fixed_witness_present':seed=='T15' or dict(r['selection'])['0']=='0','fixed_witness_kind':('hypothetical' if dict(r['selection'])['0']=='0' else None) if seed=='T10' else ('observed' if r['audit'] else 'conditional'),'exact_admitted_capture_present':seed=='T10' or r['audit'],'actual_capture_run':('run0' if r['audit'] else 'aux') if seed=='T15' else 'run0','common_ledger_family_count':count,'attained_fwer_level':'1/40','requested_level':'1/20','coverage':'open-world (excluded by profile)','manual_row_audit':r['audit']})
 return facts

def semantic_annotation_completeness(c,seed,t,o):
 spec=o['semantic_specification']
 for gindex,g in enumerate(spec['graphs']):
  if 'names' not in g:continue
  if seed in ['T06','T07','T08']:labels={n:'justified' if n in ['attacker','new-attacker'] or n.startswith('p8-inert-') else 'contested' if n=='loop' else 'defeated' for n in g['names']}
  elif seed=='T05':labels={n:'defeated' if (gindex==0 and n=='witness') or (gindex==1 and n=='attacker') else 'justified' for n in g['names']}
  elif seed in ['T11','T12']:
   selections=spec['rows'][gindex]['choices'];a,b=selections[0][1],selections[1][1]
   labels={n:'justified' for n in g['names']};labels['w']='justified' if a and b else 'defeated';labels['a1']='defeated' if a else 'justified';labels['a2']='defeated' if b else 'justified'
   expectednames=['w','a1','a2']+(['d1'] if a else [])+(['d2'] if b else []);expectededges=[['a1','w'],['a2','w']]+([['d1','a1']] if a else [])+([['d2','a2']] if b else [])
   check(g['names']==expectednames and g['edges']==expectededges and g['query_support']==['w'] and ancestors(expectededges,['w'])==set(g['query_ancestry']),c,'family graph differs from manual two-attacker graph')
  else:labels={n:'justified' for n in g['names']}
  check(g['grounded_labels']==labels,c,'grounded label annotations differ from manual graph labels')
  if seed in ['T01','T02','T03','T04','T06','T07','T08','T16']:check(not g['blocked'],c,'unexpected blocked claim annotation')
  if seed=='T05':check(g['blocked'],c,'missing blocking diagnostic')
 if spec['kind']=='family':
  check(spec['bindings']==B(t,'bindings') and spec['kind_metadata']==B(t,'kind-metadata') and spec['admitted_assumptions']==B(t,'admitted-assumptions'),c,'semantic binding metadata differs from actual bytes')
 if seed=='T15':
  rows,hs,steps,prefixes=rows_for(t,seed);truths=[]
  check(set(tuple(e[1] for e in h) for h in hs)==set(tuple(e[1] for e in h) for h in spec['histories']),c,'compatible-history set differs from independent exhaustive histories')
  for i,h in enumerate(spec['histories']):
   ids=[e[1] for e in h];caps=[e for e in ids if e in ['correct-capture','wrong-capture']];passing=len(caps)==1 and ids.index(caps[0])>ids.index('aux-run');truths.append({'history':i,'choices':[0] if passing else [],'guard':passing,'capture_run':('run0' if caps[0]=='correct-capture' else 'aux') if len(caps)==1 else None})
  check(truths==spec['guard_survival'],c,'exact nine-history guard truth table differs')

def variant_review(c,seed,t,e):
 if e['stratum']!='generated_variants':return
 original=parse((S/'inputs'/str(seed+'.sexp')).read_bytes());axis=e['source_ancestry']['axis'];level=e['source_ancestry']['level'];x=copy.deepcopy(t)
 if axis=='singleton-slots':
  added=B(x,'slots')[1+len(B(original,'slots')[1:]):]
  check(len(added)==level,c,'wrong singleton slot count')
  for i,s in enumerate(added):
   check(s[1]==['slot-id',str(1000+i)] and len(s[2])==1 and s[2][0][1]==['choice-id','0'] and s[2][0][2]==['truth'] and D(s[2][0][3][2])==['l'],c,'singleton slot is not fresh true empty fragment')
  del B(x,'slots')[1+len(B(original,'slots')[1:]):]
  for q in B(x,'requests')[1:]:
   if q[0] in ['sensitivity','slots-sensitive']:del B(q[2],'ref-choices')[1][len(B(B(original,'requests')[1][2],'ref-choices')[1]):]
  check(x==original,c,'singleton axis changes other AST fields')
 elif axis=='assumption-literals':
  oldlen=len(B(original,'assumption-catalog'));new=B(x,'assumption-catalog')[oldlen:]
  check(new==[['literal',['slot-ne',['slot-id',str(2000+i)],['choice-id','0']]] for i in range(level)],c,'added literal is not fresh undeclared inequality')
  del B(x,'assumption-catalog')[oldlen:];check(x==original,c,'assumption axis changes other AST fields')
 elif axis=='repeated-requests':
  orig=B(original,'requests')[1:];qs=B(x,'requests')[1:];check(len(qs)==level*len(orig),c,'wrong repetition count')
  labels=[]
  for i,q in enumerate(qs):
   want=copy.deepcopy(orig[i%len(orig)]);n=i//len(orig);want[1]=want[1] if not n else want[1]+'-repeat-'+str(n+1)
   check(q==want,c,'repeated request changes payload or declaration order');labels.append(q[1])
  check(len(labels)==len(set(labels)),c,'nonunique repeated labels');B(x,'requests')[:]=copy.deepcopy(B(original,'requests'));check(x==original,c,'repeated axis changes other AST fields')
 elif axis=='source-declarations':
  qs=B(t,'requests')[1:];oq=B(original,'requests')[1:]
  check([q[:2] for q in qs]==[q[:2] for q in oq],c,'source axis changes request headers')
  for q,want in zip(qs,oq):
   for side in [2,3]:
    src=q[side];old=want[side];p=D(src[2][0]);p0=D(old[2][0]);pol=D(src[2][1]);pol0=D(old[2][1]);extra=p[6][len(p0[6]):]
    expected=[]
    for i in range(level):
     ident='p8-inert-'+str(i);expected.extend([['dl',['leaf',ident,['atom',ident],['observed'],['user'],['l'],['no']]],['da',['arg',ident+'-root',['sd',ident+'-root-derived'],['et',['sl',ident]]]]])
    check(extra==expected,c,'source additions differ from fresh disconnected leaf/root groups')
    p[6]=p[6][:len(p0[6])];check(p==p0,c,'source variant changes original declarations')
    check(pol[2][3][len(pol0[2][3]):]==[['pred-sig','p8-inert-'+str(i),['l']] for i in range(level)],c,'source signature additions differ')
    pol[2][3]=pol[2][3][:len(pol0[2][3])];check(pol==pol0,c,'source variant changes original policy')
    check(src[:2]==old[:2] and src[3:]==old[3:],c,'source variant changes replay/snapshot/version')
  # Base source, process, bindings and all unrelated blocks are unchanged.
  B(x,'requests')[:]=copy.deepcopy(B(original,'requests'));check(x==original,c,'source axis changes unrelated inquiry fields')

def independent_counters(c,seed,t,o,e):
 if e['stratum']=='development_controls':return
 if seed in ENDPOINT_STATUS:
  rows=[{'selection':[]}];hs=[[]];steps=1;extension=0
 else:
  rows,hs,steps,_=rows_for(t,seed);extension=0
  for h in hs:
   prefix=1
   for slot in B(t,'slots')[1:]:
    survivors=slot[2]
    if seed=='T15':
     hn=[v[1] for v in h];captures=[e for e in hn if e in ['correct-capture','wrong-capture']];survivors=survivors if len(captures)==1 and hn.index(captures[0])>hn.index('aux-run') else []
    prefix*=len(survivors);extension+=prefix
 sources=[s for q in B(t,'requests')[1:] if q[0] in ['impact','verify-impact'] for s in q[2:4]]
 decls=sum(len(D(s[2][0])[6])-1 for s in sources)
 for r in rows:
  decls+=len(D(t[3][2][0])[6])-1
  for sid,cid in r['selection']:
   slot=next(s for s in B(t,'slots')[1:] if s[1][1]==sid);ch=next(v for v in slot[2] if v[1][1]==cid);decls+=len(D(ch[3][2]))-1
 catalog=B(t,'assumption-catalog')[1:];distinct=[v for i,v in enumerate(catalog) if v not in catalog[i+1:]];pairs=0;subsets=0
 for q in B(t,'requests')[1:]:
  if q[0] in ['impact','verify-impact']:
   graphs=GRAPHS['T01' if seed=='T16' else seed];level=e['source_ancestry'].get('level',0) if e['source_ancestry'].get('axis')=='source-declarations' else 0
   pairs+=2+sum(8+len(supp)+(len(names)+level)*len(ancestors(edges,supp)) for names,edges,supp in graphs)
  elif q[0]=='minimal-assumptions':
   subsets+=2**len(distinct)
   for n in range(len(distinct)+1):
    for ids in itertools.combinations(range(len(distinct)),n):pairs+=sum(all(truth(distinct[i],r) for i in ids) for r in rows)
  else:pairs+=len(rows)
 expected={'histories':len(hs),'sources':len(rows)+len(sources),'source-bytes':len((S/e['input_path']).read_bytes()),'declarations':decls,'search-steps':steps+extension,'pairs':pairs,'subsets':subsets}
 check(expected==e['expected_counters']['values'],c,'independently enumerated construction counters differ: '+str(expected))

def certificate_reads(c,seed,t):
 if seed not in ['T01','T02','T03','T04','T08','T16']:return
 for q in B(t,'requests')[1:]:
  if q[0]!='verify-impact':continue
  cert=q[4];want=[]
  graphs=GRAPHS['T01' if seed=='T16' else seed];level=int(c.rsplit('-',1)[1]) if '-source-declarations-' in c else 0
  for side,g in enumerate(graphs):
   names,edges,supp=copy.deepcopy(g);names.extend('p8-inert-'+str(i)+'-root' for i in range(level));carrier=list(map(str,range(len(names))));suppids=[str(names.index(v)) for v in supp];region=ancestors(edges,supp)
   def read(k,v):want.append(['reads',['side','before' if side==0 else 'after'],k,v])
   for s in suppids:read(['k-support-member',['atom','t'],s],['v-bool','true'])
   for k in ['k-reference-carrier','k-checked-carrier','k-compiled-carrier']:read([k],['v-nats',carrier])
   read(['k-blocked-closure'],['v-atoms',[]]);read(['k-blocked-query',['atom','t']],['v-bool','false']);read(['k-support-nodes',['atom','t']],['v-nats',suppids]);read(['k-hole-nodes',['atom','t']],['v-nats',[]])
   for i,name in enumerate(names):
    for j,target in enumerate(names):
     if target in region:read(['k-attack-edge',str(i),str(j)],['v-bool',boolwire([name,target] in edges)])
   read(['k-whole-input'],['v-source',q[2+side]])
  if q[1]=='tampered':
   r=next(r for r in want if r[2][0]=='k-blocked-query');r[3]=['v-bool','true']
  check(want==cert[20],c,'certificate exact ordered read evidence differs from manual graph/source facts')
  check(cert[4:6]==[[],[]] and cert[6:8]==[q[2][3],q[3][3]],c,'certificate backend snapshot/replay differs')
  check(cert[17:20]==[[],[],[[['atom','t'],boolwire(LOCALITY[seed])]]],c,'certificate graph difference or locality facts differ')

for e in M['cases']:
 c=e['case_id'];data=(S/e['input_path']).read_bytes();odata=(S/e['oracle_path']).read_bytes();t=parse(data);o=json.loads(odata)
 check(digest(data)==e['input_sha256'],c,'input manifest hash differs');check(digest(odata)==e['oracle_sha256'],c,'oracle manifest hash differs')
 check(e['query_order']==[q[1] for q in B(t[2],'queries')[1:]]+[q[1] for q in B(t,'requests')[1:]],c,'query order differs')
 check(e['catalog']==B(t,'assumption-catalog')[1:],c,'manifest catalog differs')
 check(o['expected']['result_kind']=='results' and o['expected']['exit_code']==0,c,'unexpected refusal classification')
 for key,value in e['expected_counters']['values'].items():check(value<=e['effective_declared_limits'][key],c,'expected counter exceeds cap: '+key)
 if e['stratum']=='development_controls':
  a=e['source_ancestry'];check(data==(ROOT/a['input_path']).read_bytes(),c,'legacy control input changed');check(digest((ROOT/a['golden_path']).read_bytes())==a['golden_sha256'],c,'legacy golden hash changed')
  gold=[parse(line) for line in (ROOT/a['golden_path']).read_bytes().splitlines() if line];check(gold==o['expected']['results'],c,'legacy golden AST differs');legacy_evidence.append({'case_id':c,'role':'development control; copied original golden, not new independent semantic evidence','input_sha256':digest(data),'oracle_sha256':digest(odata),'source_input_sha256':a['input_sha256'],'source_golden_sha256':a['golden_sha256'],'semantic_content_sha256':digest((json.dumps({'expected':o['expected'],'semantic_specification':o['semantic_specification']},sort_keys=True,separators=(',',':'),ensure_ascii=False)+'\n').encode('utf-8'))});continue
 seed=c[:3]
 if seed=='T07':
  # These facts require fresh review of the decoded candidate source, rather
  # than carrying the old graph annotation across changed input bytes.
  req=B(t,'requests')[1]
  before,after=req[2:4]
  bp,ap=D(before[2][0]),D(after[2][0]);bpol,apol=D(before[2][1]),D(after[2][1])
  oldrule=next(r for r in bpol[3][1:] if r[1]=='r-s')
  fresh=copy.deepcopy(oldrule);fresh[1]='r-s-new'
  check(apol[3]==bpol[3]+[fresh],c,'T07 after policy must add only the fresh cloned r-s-new rule')
  oldargs={d[1][1]:d for d in bp[6][1:] if d[0]=='da'}
  newargs={d[1][1]:d for d in ap[6][1:] if d[0]=='da'}
  check(all(newargs.get(n)==d for n,d in oldargs.items()),c,'T07 existing arguments changed')
  added=copy.deepcopy(oldargs['attacker']);added[1][1]='new-attacker';added[1][2]=['sd','new-attack-claim'];added[1][3][1]='r-s-new'
  check(newargs.get('new-attacker')==added,c,'T07 new-attacker is not the distinct cloned-rule instance')
  kept=[d for d in ap[6] if d!=added and d!=['dk',['sreb','new-attacker','witness']]]
  check(kept==bp[6] and sum(d==added for d in ap[6])==1 and sum(d==['dk',['sreb','new-attacker','witness']] for d in ap[6])==1,c,'T07 declarations differ from the proposed additive recipe')
  check(all(a[1][3][1]!='r-s-new' for n,a in newargs.items() if n!='new-attacker' and a[1][3][0]=='it'),c,'T07 existing term references new rule')
 variant_review(c,seed,t,e);independent_counters(c,seed,t,o,e);certificate_reads(c,seed,t)
 audit_facts=manual_audit_binding_review(c,seed,t,o)
 semantic_annotation_completeness(c,seed,t,o)
 if seed in ENDPOINT_STATUS:endpoint_review(c,seed,t,o)
 else:family_review(c,seed,t,o)
 evidence[-1]['input_sha256']=digest(data);evidence[-1]['oracle_sha256']=digest(odata)
 evidence[-1]['semantic_content_sha256']=digest((json.dumps({'expected':o['expected'],'semantic_specification':o['semantic_specification']},sort_keys=True,separators=(',',':'),ensure_ascii=False)+'\n').encode('utf-8'))
 evidence[-1]['expected_sha256']=digest(json.dumps(o['expected'],sort_keys=True,separators=(',',':')).encode());evidence[-1]['semantic_specification_sha256']=digest(json.dumps(o['semantic_specification'],sort_keys=True,separators=(',',':')).encode())
 if audit_facts is not None:evidence[-1]['independent_audit_binding_facts']=audit_facts
 if seed in GRAPHS:evidence[-1]['manual_endpoint_graphs']=GRAPHS[seed]

axes=[('singleton-slots',[0,1,4,40],['T09','T10','T11','T12']),('source-declarations',[0,1,4,16],['T01','T05','T06','T07']),('assumption-literals',[0,1,2,4],['T09','T10','T13','T14']),('repeated-requests',[1,2,4,8],['T01','T05','T11','T12'])]
expected_new_ids={f'T{i:02}' for i in range(1,17)}|{f'{seed}-{axis}-{level}' for axis,levels,seeds in axes for seed in seeds for level in levels}
check({e['case_id'] for e in M['cases'] if e['stratum']!='development_controls'}==expected_new_ids,'manifest','approved seed/axis/level case identities differ')
check(len(M['cases'])==96,'manifest','wrong total')
check([sum(e['stratum']==s for e in M['cases']) for s in ['development_controls','authored_controls','generated_variants']]==[16,16,64],'manifest','wrong strata')
groups={}
for e in M['cases']:groups.setdefault(e['input_sha256'],[]).append(e['case_id'])
check(len(groups)==M['unique_input_count'],'manifest','unique hash denominator differs')
check([{'input_sha256':h,'case_ids':ids} for h,ids in groups.items() if len(ids)>1]==M['duplicate_content_groups'],'manifest','duplicate content disclosure differs')
protocol=json.loads((S/'protocol.json').read_text());amendment=next(a for a in protocol['amendments'] if a['id']=='source-axis-groups')
check(amendment['provenance']=='user' and amendment['approval_text']=='Count leaf-root groups; clarify the protocol accordingly (Recommended)' and digest(amendment['approval_text'].encode())==amendment['approval_text_sha256'],'protocol','source axis clarification lacks explicit user approval')

report={'schema':'inquiry-p8-independent-review','schema_version':1,'status':('FAIL' if findings else 'PASS') if args.reviewer else 'AUTHORING-CHECK','reviewer':args.reviewer or 'pending-independent-review','provenance':'ai-executed','driver_outputs_used':False,'analysis_implementation_imported':False,'method':'Manual source-byte inspection of bounded graphs and capture/ledger provenance; independent exhaustive permutations, guarded selections, catalog subsets, declaration-ordered realizers; exact decoded AST comparison. Legacy goldens remain development controls. This is not a source checker.','references':['docs/theory-process.md#what-do-the-exact-inquiry-analyses-compute','docs/theory-process.md#what-does-graph-difference-locality-prove','docs/theory-process.md#how-is-an-edits-impact-certified','docs/theory-process.md#what-does-the-inquiry-wrapper-add'],'approved_source_axis_amendment':amendment,'reviewed_protocol_sha256':digest((S/'protocol.json').read_bytes()),'reviewed_author_generator_sha256':digest((ROOT/'scripts/inquiry_evaluation_cases.py').read_bytes()),'reviewed_certificate_producer_sha256':digest((ROOT/'scripts/inquiry-impact-producer.hs').read_bytes()),'reviewed_manifest_sha256':digest((S/'MANIFEST.json').read_bytes()),'tool_path':str(Path(__file__).resolve().relative_to(ROOT)),'tool_sha256':digest(Path(__file__).read_bytes()),'exact_expected_ast_checks':sum(x['exact_expected_ast_equal'] for x in evidence),'new_case_count':len(evidence),'legacy_controls_checked':16,'unique_inputs_checked':len(groups),'findings':findings,'case_evidence':evidence,'development_control_evidence':legacy_evidence}
if args.out is not None:
 try:
  with args.out.open('x',encoding='utf-8') as receipt:
   receipt.write(json.dumps(report,indent=2)+'\n')
 except OSError as error:
  parser.error('cannot create fresh review receipt: '+str(error))
print(json.dumps({'status':report['status'],'exact_checks':report['exact_expected_ast_checks'],'cases':len(evidence),'findings':findings},indent=2))
sys.exit(1 if findings else 0)
