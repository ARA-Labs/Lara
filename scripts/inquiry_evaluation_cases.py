#!/usr/bin/env python3
"""Deterministic P8 structural authoring and finite annotated-table oracles.

This is an evaluation author, never a source checker. Graphs and public statuses
are hand-specified below; only finite table comparisons and catalog subsets are
enumerated. New expected results are never read from inquiry-driver output.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
import hashlib
import itertools
import json
from pathlib import Path
from evidence_measured import canonical, parse, wire
ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / 'evaluation/inquiry-p8'
RECIPE_VERSION = 'inquiry-p8-recipes@1'
CORRECTED_RECIPE = 'inquiry-p8-recipes@2-candidate'
FIXTURES = ROOT / 'fixtures/process/inquiry'

def block(tree, name):
    matches = [x for x in tree if isinstance(x,list) and x and x[0]==name]
    assert len(matches)==1,(name,len(matches))
    return matches[0]
def fixture(name): return parse((FIXTURES / (name+'.sexp')).read_bytes())
def sha(data): return hashlib.sha256(data).hexdigest()
def js(data): return (json.dumps(data,indent=2,ensure_ascii=False)+'\n').encode()
def uncons(value):
    result=[]
    while value[0]=='cons': result.append(value[1]);value=value[2]
    assert value==['nil'];return result
def decode_datum(value):
    if value[0]=='node': return [value[1]]+[decode_datum(x) for x in uncons(value[2])]
    if value[0]=='string': return value[1]
    assert value[0].startswith('integer');return value

def encode_datum(value):
    if isinstance(value,str): return ['string',value]
    if value[0].startswith('integer'): return value
    tail=['nil']
    for item in reversed(value[1:]): tail=['cons',encode_datum(item),tail]
    return ['node',value[0],tail]
def program(source): return decode_datum(source[2][0])
def policy(source): return decode_datum(source[2][1])
def put_program(source,value): source[2][0]=encode_datum(value)
def put_policy(source,value): source[2][1]=encode_datum(value)
def empty_fragment(): return ['checked-fragment','1',encode_datum(['l'])]
def slot(ident, fragments):
    return ['slot',['slot-id',str(ident)],[['choice',['choice-id',str(i)],['truth'],['checked-fragment','1',encode_datum(['l']+frag)]] for i,frag in enumerate(fragments)]]
def leaf(ident,atom): return ['dl',['leaf',ident,['atom',atom],['observed'],['user'],['l'],['no']]]
def leaf_arg(ident,leafid): return ['da',['arg',ident,['sd',ident+'-derived'],['et',['sl',leafid]]]]
def blank(claim='c0'):
    tree=fixture('reference-sensitivity');tree[3]=deepcopy(fixture('impact-rejected')[-1][1][3])
    block(block(tree[2],'names'),'claim')[:]=['claim',claim]
    block(tree,'slots')[:]=['slots'];block(tree,'bindings')[:]=['bindings',[['claim-binding',claim,'claim',['atom','t']]],[]]
    block(tree,'requests')[:]=['requests'];return tree

def literal(kind,slotid,choiceid):return ['literal',[kind,['slot-id',str(slotid)],['choice-id',str(choiceid)]]]
def observable(claim='c0'):return ['observable',['status-obs',claim]]
def target(status,claim='c0'):return ['target',['status-target',claim,status]]
def boolatom(value):return 'true' if value else 'false'
JUST=['published','justified'];DEFEATED=['published','defeated']
# Annotated graphs are stable identities, with independently authored edges.
def graph(names,edges,region,support,blocked=False):
    return {'names':names,'edges':edges,'query_ancestry':region,'query_support':support,'blocked':blocked}
G_PLAIN=graph(['witness'],[],['witness'],['witness'])
# Old blocked graph has two attackers; retained attacker disappears in after.
G_BLOCK_BEFORE=graph(['witness','attacker'],[['attacker','witness']],['witness','attacker'],['witness'],True)
G_BLOCK_AFTER=graph(['witness'],[],['witness'],['witness'],True)

def impact_spec(before,after,status_before,status_after,locality,graphs,rejections=(None,None)):
    acceptance=[status_before is not None,status_after is not None]
    transition=('accepted' if acceptance[0] else 'rejected')+'-to-'+('accepted' if acceptance[1] else 'rejected')
    changed=status_before!=status_after
    result=['impact-result',['transition',transition],[['query-impact',['atom','t'],[] if status_before is None else [status_before],[] if status_after is None else [status_after],boolatom(changed),boolatom(locality)]],[['atom','t']] if changed else [],[] if changed else [['atom','t']]]
    return {'kind':'impact','statuses':[status_before,status_after],'rejections':list(rejections),'graphs':graphs,'transition':transition,'expected_body':['impact-body',result], 'locality':locality,
        'locality_reason':'stable support identities and equal relevant incoming edges' if locality else 'relevant ancestry or acceptance differs',
        'wire_boundary':'impact-result omits endpoint rejection payloads; annotations are not runtime telemetry',
        'histories':[[]], 'history_search_steps':1, 'row_truth_table':[], 'assumption_truth_table':[],
        'process_scope':'Empty process history; endpoint analyses do not consume process assurance.'}

def impact_case(name,before,after,spec):
    tree=blank();tree[3]=deepcopy(before);block(tree,'requests').append(['impact',name,before,after,['queries','c0']]);return tree,spec

def history_events(tree,names):
    events={x[1]:x[:3] for x in block(tree[2],'record')[1:] if x[0]=='event'}
    events.update({x[1]:x for x in block(tree[2],'universe')[1:]})
    return [events[n] for n in names]

def family_spec(tree,assignments,statuses,audits=None,histories=None,history_steps=1,graphs=None):
    histories=[[]] if histories is None else histories
    assert len(assignments)==len(statuses)
    rows=[]
    for h in histories:
        for i,a in enumerate(assignments):
            rows.append({'history':deepcopy(h),'choices':a,'status':deepcopy(statuses[i]),'rejection':None,'audit':None if audits is None else audits[i]})
    return {'kind':'family','rows':rows,'histories':histories,'history_search_steps':history_steps,'graphs':graphs or [],
        'bindings':deepcopy(block(tree,'bindings')),'kind_metadata':deepcopy(block(tree,'kind-metadata')),
        'admitted_assumptions':deepcopy(block(tree,'admitted-assumptions')),
        'assumption_truth_table':[]}

def completion(tree,row):
    selections=[]
    for s,c in row['choices']:
        authored=next(x for x in block(tree,'slots')[1:] if x[1][1]==str(s))
        choice=next(x for x in authored[2] if x[1][1]==str(c))
        selections.append(['selection',authored[1],deepcopy(choice)])
    return ['completion',row['history'],selections]
def assignment(row):return [[['slot-id',str(s)],['choice-id',str(c)]] for s,c in row['choices']]
def table_holds(lit,row):
    body=lit[1];assert body[0] in ['slot-eq','slot-ne'],'only approved slot table literals'
    selected=dict(row['choices']).get(int(body[1][1]));equal=selected==int(body[2][1]);return equal if body[0]=='slot-eq' else not equal

def family_bodies(tree,spec):
    rows=spec['rows'];accepted=[r for r in rows if r['rejection'] is None];bodies=[]
    counts=[str(len(rows)),str(len(accepted)),str(len(rows)-len(accepted))]
    catalog=block(tree,'assumption-catalog')[1:];distinct=[]
    for item in catalog:
        if item in distinct:distinct.remove(item)
        distinct.append(item)
    truths=[[table_holds(lit,row) for lit in distinct] for row in rows]
    spec['assumption_truth_table']=[{'row':i,'values':v} for i,v in enumerate(truths)]
    for req in block(tree,'requests')[1:]:
        kind=req[0]
        if kind in ['status','audit']:
            key='status' if kind=='status' else 'audit'
            values=[['family-row' if key=='status' else 'family-audit-row',r['history'],assignment(r),[] if r['rejection'] is None else [r['rejection']],[] if r['rejection'] is not None else ([r[key]] if key=='status' else [boolatom(r[key])])] for r in rows]
            verdict=(bool(rows) and all((r['rejection'],r['status'])==(rows[0]['rejection'],rows[0]['status']) for r in rows)) if kind=='status' else (bool(rows) and len(accepted)==len(rows) and all(r['audit'] for r in rows) and spec.get('coverage_accepted',False))
            body=[kind+'-body',['family-'+kind+'-result',values]+counts+[boolatom(verdict)]]
        elif kind=='stable':
            obs=req[2];key='status' if obs[1][0]=='status-obs' else 'audit'
            vals=[('rejected',r['rejection']) if r['rejection'] is not None else ('accepted',r[key]) for r in rows]
            whole=bool(vals) and all(x==vals[0] for x in vals)
            domain=bool(accepted) and all(r[key]==accepted[0][key] for r in accepted)
            body=['stability-body',['stability-result',obs]+counts+[boolatom(whole),boolatom(domain)]]
        elif kind in ['sensitivity','slots-sensitive']:
            ref=req[2];rhist=block(ref,'ref-history')[1];rchoices=[(int(x[0][1]),int(x[1][1])) for x in block(ref,'ref-choices')[1]]
            reference=next(r for r in rows if r['history']==rhist and r['choices']==rchoices)
            key='status' if req[3][1][0]=='status-obs' else 'audit'
            def val(r):return ('rejected',r['rejection']) if r['rejection'] is not None else ('accepted',r[key])
            differing=[r for r in rows if val(r)!=val(reference)]
            def changed(r):return [s for s,c in reference['choices'] if dict(r['choices']).get(s)!=c]
            same=[r for r in differing if r['history']==reference['history']]
            flips=[]
            for r in same:
                x=changed(r)
                if x and x not in flips:flips.append(x)
            minima=[x for x in flips if not any(set(y)<set(x) for y in flips)]
            body=[kind+'-body',['sensitivity-result',req[3],completion(tree,reference),str(len(rows)),str(len(differing)),[['row',completion(tree,r),[['slot-id',str(s)] for s in changed(r)]] for r in differing],[[['slot-id',str(s)] for s in x] for x in minima],[[[['slot-id',str(s)] for s in x],completion(tree,next(r for r in same if changed(r)==x))] for x in minima]]]
        elif kind=='minimal-assumptions':
            t=req[2];key='status' if t[1][0]=='status-target' else 'audit'
            expected=t[1][2] if key=='status' else True
            subsets=[list(x) for n in range(len(distinct)+1) for x in itertools.combinations(range(len(distinct)),n)]
            # Exact table enumeration, with a nonempty rejection-free restriction.
            restricted=lambda ids:[i for i,v in enumerate(truths) if all(v[j] for j in ids)]
            passing=lambda ids:bool(restricted(ids)) and all(rows[i]['rejection'] is None and rows[i][key]==expected for i in restricted(ids))
            good=[ids for ids in subsets if passing(ids)]
            minima=[ids for ids in good if not any(set(other)<set(ids) for other in good)]
            sets=[]
            for ids in minima:
                deletions=[]
                for j in ids:
                    survivors=restricted([k for k in ids if k!=j]);counter=next((i for i in survivors if rows[i]['rejection'] is not None or rows[i][key]!=expected),None)
                    deletions.append(['deletion',distinct[j],[completion(tree,rows[i]) for i in survivors],[] if counter is None else [completion(tree,rows[counter])]])
                sets.append(['minimal-set',[distinct[j] for j in ids],[completion(tree,rows[i]) for i in restricted(ids)],deletions])
            spec['catalog_subsets']=[{'indices':ids,'surviving_rows':restricted(ids),'satisfies':passing(ids)} for ids in subsets]
            body=['assumptions-body',['assumption-result',t,catalog,str(len(rows)),sets]]
        else:raise ValueError(kind)
        bodies.append(['inquiry-result','1',req[1],body])
    return bodies

DUP=['source',['source',['structural',['duplicate-leaf-id','seed']]]]
G_REJECT=graph([],[],[],[])
G_BLOCK_BEFORE=graph(['witness','attacker'],[['attacker','witness']],['witness','attacker'],['witness'],True)
G_BLOCK_AFTER=graph(['witness','attacker','defender'],[['attacker','witness'],['defender','attacker']],['witness','attacker','defender'],['witness'],True)
G_UNRELATED=graph(['witness','consumer','attacker'],[['attacker','witness'],['attacker','consumer']],['witness','attacker'],['witness'])

def source_pin_everywhere(tree,old,new):
    # Structural equality replacement of whole typed source bindings, never text.
    if tree==old:return deepcopy(new)
    if isinstance(tree,list):return [source_pin_everywhere(x,old,new) for x in tree]
    return tree

def approved_prefix_table(events,prerequisites):
    """Enumerate an approved concrete event-dependency table, without a checker."""
    prefixes=[]
    for n in range(len(events)+1):
        for prefix in itertools.permutations(events,n):
            if any(e in prefix and any(p not in prefix or prefix.index(p)>prefix.index(e) for p in required) for e,required in prerequisites.items()):continue
            prefixes.append(list(prefix))
    positions={e:i for i,e in enumerate(events)}
    return sorted(prefixes,key=lambda prefix:tuple(positions[e] for e in prefix))

def authored():
    result={};pair=deepcopy(block(fixture('impact-rejected'),'requests')[1]);bad,good=pair[2:4]
    for name,b,a,sb,sa,loc,gb,ga,rb,ra in [
        ('T01',good,good,JUST,JUST,True,G_PLAIN,G_PLAIN,None,None),
        ('T02',good,bad,JUST,None,False,G_PLAIN,G_REJECT,None,DUP),
        ('T03',bad,good,None,JUST,False,G_REJECT,G_PLAIN,DUP,None),
        ('T04',bad,bad,None,None,False,G_REJECT,G_REJECT,DUP,DUP)]:
        result[name]=impact_case(name,deepcopy(b),deepcopy(a),impact_spec(b,a,sb,sa,loc,[deepcopy(gb),deepcopy(ga)],(rb,ra)))
    # Absent statuses never enter the unchanged accepted-query partition.
    result['T04'][1]['expected_body'][1][-1]=[]
    for name,control,sb,sa,loc,graphs in [
        ('T05','blocked-conditional',['evidence-blocked','defeated'],['evidence-blocked','justified'],False,[G_BLOCK_BEFORE,G_BLOCK_AFTER]),
        ('T06','unrelated-self-attack',DEFEATED,DEFEATED,True,[G_UNRELATED,graph(['witness','consumer','attacker','loop'],[['attacker','witness'],['attacker','consumer'],['loop','loop']],['witness','attacker'],['witness'])])]:
        req=block(fixture(control),'requests')[1]
        tree,spec=impact_case(name,deepcopy(req[2]),deepcopy(req[3]),impact_spec(req[2],req[3],sb,sa,loc,deepcopy(graphs)))
        # Keep exact declaration binding from the source fixture.
        block(tree,'bindings')[1]=deepcopy(block(fixture(control),'bindings')[1]);result[name]=(tree,spec)
    before=deepcopy(result['T06'][0][-1][1][2]);after=deepcopy(before);p=program(after)
    original=next(x for x in p[6][1:] if x[0]=='da' and x[1][1]=='attacker');extra=deepcopy(original);extra[1][1]='new-attacker';extra[1][2]=['sd','new-attack-claim']
    if RECIPE_VERSION == CORRECTED_RECIPE:
        pol=policy(after);fresh=deepcopy(next(r for r in pol[3][1:] if r[1]=='r-s'));fresh[1]='r-s-new';pol[3].append(fresh);put_policy(after,pol)
        extra[1][3][1]='r-s-new'
    p[6].extend([extra,['dk',['sreb','new-attacker','witness']]]);put_program(after,p)
    gafter=graph(['witness','consumer','attacker','new-attacker'],[['attacker','witness'],['attacker','consumer'],['new-attacker','witness'],['new-attacker','consumer']],['witness','attacker','new-attacker'],['witness'])
    result['T07']=impact_case('T07',before,after,impact_spec(before,after,DEFEATED,DEFEATED,False,[deepcopy(G_UNRELATED),gafter]))
    result['T07'][1]['specification']='Hand graph: attacker defeats witness and its consumer. Add a second unattacked attacker of witness, whose attack also propagates to consumer. Witness remains defeated; incoming ancestry changes.'
    perm=deepcopy(before);p=program(perm);ds=p[6];at=next(i for i,x in enumerate(ds) if isinstance(x,list) and x[0]=='da' and x[1][1]=='attacker');arg=ds.pop(at);ds.insert(3,arg);put_program(perm,p)
    gperm=deepcopy(G_UNRELATED);gperm['names']=['attacker','witness','consumer'];gperm['query_ancestry']=['attacker','witness']
    result['T08']=impact_case('T08',before,perm,impact_spec(before,perm,DEFEATED,DEFEATED,True,[deepcopy(G_UNRELATED),gperm]))
    result['T08'][1]['support_correspondence']=[['witness','witness']];result['T08'][1]['specification']='Permute independent attacker before witness; consumer still follows its prerequisite witness. Compare stable argument identities, not compact indices.'
    tree=blank();tree[3]=deepcopy(bad);block(tree,'slots').append(slot(0,[[],[]]));block(tree,'requests').extend([['status','status','c0'],['stable','stable',observable()],['minimal-assumptions','minimal',target(JUST)]])
    block(tree,'assumption-catalog').extend([literal('slot-eq',0,0),literal('slot-ne',0,0)])
    spec=family_spec(tree,[[(0,0)],[(0,1)]],[None,None],graphs=[{'outcome':'duplicate leaf seed before graph construction'}]);
    for row in spec['rows']:row['rejection']=deepcopy(DUP)
    spec['specification']='Both truth-guarded empty choices materialize the same duplicate-leaf source. Whole rejection equality true; accepted-only domain empty and unstable.';result['T09']=(tree,spec)
    tree=fixture('fixed-witness');profile=deepcopy(block(tree,'requests')[1][4]);obs=['observable',['audit-obs','c0','w0',profile]]
    block(tree,'requests')[:]=['requests',['status','status','c0'],['audit','audit','c0','w0',profile],['stable','status-stability',observable()],['stable','audit-stability',obs],['minimal-assumptions','minimal',['target',['audit-target','c0','w0',profile]]]]
    block(tree,'assumption-catalog').extend([literal('slot-eq',0,0),literal('slot-ne',0,1)])
    history=history_events(tree,['commit','read','run','success'])
    spec=family_spec(tree,[[(0,0)],[(0,1)]],[JUST,JUST],[True,False],[history],history_steps=14,graphs=[graph(['witness'],[],['witness'],['witness']),graph(['defender'],[],['defender'],['defender'])]);spec['specification']='First choice supplies submitted witness; second supplies distinct defender. Both are unattacked claim supports. Fixed witness is absent in second row; alternative support cannot substitute.';result['T10']=(tree,spec)
    for name,control in [('T11','reference-sensitivity'),('T12','joint-only')]:
        tree=fixture(control)
        if name=='T11':
            third=deepcopy(block(tree,'slots')[1][2][1]);third[1][1]='2';block(tree,'slots')[1][2].append(third)
        req=deepcopy(block(tree,'requests')[1]);req[0]='sensitivity';req[1]='sensitivity';other=deepcopy(req);other[0]='slots-sensitive';other[1]='slots';block(tree,'requests')[:]=['requests',req,other,['status','status','claim']]
        assignments=[[(0,a),(1,b)] for a in range(3 if name=='T11' else 2) for b in range(2)]
        statuses=[JUST if a and b else DEFEATED for (_,a),(_,b) in assignments]
        graphs=[]
        for (_,a),(_,b) in assignments:
            names=['w','a1','a2']+(['d1'] if a else [])+(['d2'] if b else []);edges=[['a1','w'],['a2','w']]+([['d1','a1']] if a else [])+([['d2','a2']] if b else [])
            graphs.append(graph(names,edges,names,['w']))
        spec=family_spec(tree,assignments,statuses,graphs=graphs);spec['specification']='Two independent attackers require both defenders. Singleton changes leave witness defeated. T11 choice 2 reproduces choice 1 exactly; row flips retained and minimum slot pair deduplicated.';result[name]=(tree,spec)
    for name in ['T13','T14']:
        tree=blank();block(tree,'slots').append(slot(0,[[],[]]));block(tree,'assumption-catalog').extend([literal('slot-eq',0,0),literal('slot-ne',0,0)] if name=='T13' else [literal('slot-ne',900,0),literal('slot-ne',901,0)])
        desired=DEFEATED if name=='T13' else JUST
        block(tree,'requests').extend([['status','status','c0'],['minimal-assumptions','minimal',target(desired)]])
        spec=family_spec(tree,[[(0,0)],[(0,1)]],[JUST,JUST],graphs=[deepcopy(G_PLAIN),deepcopy(G_PLAIN)]);spec['specification']='Unattacked witness justified in every row. '+('Defeated target unreachable; contradictory catalog full set has empty restriction and fails.' if name=='T13' else 'Common justified target already true; undeclared inequalities always true and empty set is the unique minimum.')
        result[name]=(tree,spec)
    # Two actual process bindings: only the exact admitted run0 capture passes.
    # The auxiliary run is in another family, preserving the common ledger bound.
    tree=fixture('fixed-witness');base=deepcopy(tree[3]);p=program(base);p[6].append(['da',['arg','witness',['sc','claim'],['et',['sl','first']]]]);put_program(base,p)
    old=deepcopy(tree[3]);tree=source_pin_everywhere(tree,old,base);tree[3]=base
    names=block(tree[2],'names');block(names,'event').extend(['aux-run','correct-capture','wrong-capture']);block(names,'run').append('aux');block(names,'family').append('other-family')
    auxiliary=['event','aux-run',['run','aux','plan','0',['inputs'],'other-family']]
    block(tree[2],'record').extend([auxiliary+[['at','fixture.md','aux']],['order','success','aux-run',['at','fixture.md','aux-order']]])
    correct=['event','correct-capture',['result','run0','2']];wrong=['event','wrong-capture',['result','aux','2']]
    block(tree[2],'universe').extend([correct,wrong])
    # Exactly one capture after the auxiliary run. This excludes absent capture,
    # both captures and all earlier captures without changing observed metadata.
    guard=['or',['and',['before',auxiliary,correct],['not',['present',wrong]]],['and',['before',auxiliary,wrong],['not',['present',correct]]]]
    declared_slot=slot(0,[[]]);declared_slot[2][0][2]=guard;block(tree,'slots')[:]=['slots',declared_slot]
    block(tree,'bindings')[2]=block(tree,'bindings')[2][:1]
    block(tree,'kind-metadata')[:]=[block(tree,'kind-metadata')[0]]+[k for k in block(tree,'kind-metadata')[1:] if k[2] in [['leaf','first'],['argument','witness']]]
    block(tree,'admitted-assumptions')[:]=[block(tree,'admitted-assumptions')[0]]+[a for a in block(tree,'admitted-assumptions')[1:] if a[3] in [['leaf','first'],['argument','witness']]]
    for a in block(tree,'admitted-assumptions')[1:]:a[4]=deepcopy(correct)
    profile=deepcopy(profile);profile[1]=['observed'];block(tree,'requests')[:]=['requests',['status','status','c0'],['audit','audit','c0','w0',profile],['stable','status-stability',observable()],['stable','audit-stability',['observable',['audit-obs','c0','w0',profile]]]]
    events=['commit','read','run','success','aux-run','correct-capture','wrong-capture']
    prerequisites={'run':['commit'],'success':['run'],'aux-run':['commit'],'correct-capture':['run'],'wrong-capture':['aux-run']}
    prefixes=approved_prefix_table(events,prerequisites)
    # Record order is the independently specified five-event chain. This finite
    # truth table retains every compatible prefix, including excluded guard rows.
    common=['commit','read','run','success','aux-run'];compatible=[h for h in prefixes if all(e in h for e in common) and [e for e in h if e in common]==common]
    assert len(compatible)==9
    histories=[history_events(tree,h) for h in compatible]
    spec=family_spec(tree,[],[],history_steps=len(prefixes),graphs=[graph(['witness'],[],['witness'],['witness'])]);spec['histories']=histories
    spec['executable_prefix_table']=prefixes;spec['history_prefix_prerequisites']=prerequisites;spec['compatible_history_event_ids']=compatible;spec['guard_survival']=[]
    for index,h in enumerate(compatible):
        captures=[e for e in h if e in ['correct-capture','wrong-capture']]
        survives=len(captures)==1 and h.index(captures[0])>h.index('aux-run')
        spec['guard_survival'].append({'history':index,'choices':[0] if survives else [],'guard':survives,'capture_run':('run0' if captures[0]=='correct-capture' else 'aux') if len(captures)==1 else None})
        if survives:spec['rows'].append({'history':histories[index],'choices':[(0,0)],'status':deepcopy(JUST),'rejection':None,'audit':captures[0]=='correct-capture'})
    assert [r['audit'] for r in spec['rows']]==[True,False]
    spec['specification']='Common ledger binds exact run0/fam/result1 in both rows. A required auxiliary run belongs to other-family, so ledger count for fam remains one. Unchanged observed metadata and admitted captures bind source base and exact Result(run0,2). Correct-capture row is observed and audit true; wrong-capture row carries actual Result(aux,2), fails exact process/run capture binding, stays conditional and audit false. Guard admits exactly one capture after auxiliary run. Both rows retain the same justified witness; no label alone earns observed assurance.';result['T15']=(tree,spec)
    for name in ['T10','T15']:
        tree,spec=result[name]
        spec['audit_profile']=deepcopy(next(r[4] for r in block(tree,'requests')[1:] if r[0]=='audit'))
        spec['coverage_annotation']={'admitted':['open-world'],'profile_accepts':['complete','count-bounded'],'all_admitted_coverage_accepted':False,'source':'default open-world because the process record contains no coverage admission'}
        spec['audit_components']=[]
        for i,row in enumerate(spec['rows']):
            spec['audit_components'].append({'row':i,'source_binding_matches_family_base':True,'claim_binding_matches':True,'kind_metadata_complete':True,'provenance_keys_known':True,'selected_argument_present':name=='T15' or i==0,'selected_argument_grounded_justified':name=='T15' or i==0,'selected_grade':('observed' if row['audit'] else 'conditional') if name=='T15' else ('hypothetical' if i==0 else None),'capture_event_present':row['audit'] if name=='T15' else True,'actual_capture_event_present':True,'actual_capture_run':('run0' if row['audit'] else 'aux') if name=='T15' else 'run0','capture_source_and_run_exact':row['audit'] if name=='T15' else True,'ledger_common_run':'run0','ledger_common_family':'fam','ledger_result':1,'ledger_count':1,'ledger_count_bound':1,'warranted_fwer_level':'1/40','required_profile_level':'1/20','required_sampling_probe_present':True,'row_audit':row['audit']})
        spec['annotation_boundary']='Profile, coverage, kind completeness and binding facts are independently authored construction annotations; family audit output exposes only the final per-row booleans.'
        if name=='T10':
            events=['commit','read','run','success'];prerequisites={'run':['commit'],'success':['run']}
            prefixes=approved_prefix_table(events,prerequisites)
            assert len(prefixes)==spec['history_search_steps']
            spec['executable_prefix_table']=prefixes;spec['history_prefix_prerequisites']=prerequisites
    for name,(tree,spec) in result.items():
        if spec['kind']=='impact':
            spec['row_truth_table']=[{'endpoint':side,'accepted':value is not None,'status':value,'rejection':spec['rejections'][i]} for i,(side,value) in enumerate(zip(['before','after'],spec['statuses']))]
        for i,g in enumerate(spec.get('graphs',[])):
            if 'names' not in g:continue
            if name in ['T07','T08','T06']:
                g['grounded_labels']={n:('justified' if n in ['attacker','new-attacker'] else 'contested' if n=='loop' else 'defeated') for n in g['names']}
            elif name=='T05':
                g['grounded_labels']={n:('defeated' if (i==0 and n=='witness') or (i==1 and n=='attacker') else 'justified') for n in g['names']}
            elif name in ['T11','T12']:
                choices=dict(spec['rows'][i]['choices']);g['grounded_labels']={n:('justified' if n.startswith('d') or (n=='w' and all(choices.values())) else 'defeated' if n=='w' or (n=='a1' and choices[0]) or (n=='a2' and choices[1]) else 'justified') for n in g['names']}
            else:g['grounded_labels']={n:'justified' for n in g['names']}
    return result

AXES=[('singleton-slots',[0,1,4,40],['T09','T10','T11','T12']),('source-declarations',[0,1,4,16],['T01','T05','T06','T07']),('assumption-literals',[0,1,2,4],['T09','T10','T13','T14']),('repeated-requests',[1,2,4,8],['T01','T05','T11','T12'])]

def inert_source(source,count):
    p=program(source);pol=policy(source)
    for i in range(count):
        ident=f'p8-inert-{i}'
        p[6].extend([leaf(ident,ident),leaf_arg(ident+'-root',ident)])
        pol[2][3].append(['pred-sig',ident,['l']])
    put_program(source,p);put_policy(source,pol)

def vary(tree,spec,axis,level):
    tree=deepcopy(tree);spec=deepcopy(spec)
    spec['variant']={'axis':axis,'level':level,'only_designated_axis_changed':True}
    if axis=='singleton-slots':
        for i in range(level):
            ident=1000+i;block(tree,'slots').append(slot(ident,[[]]))
            for row in spec['rows']:row['choices'].append((ident,0))
            for req in block(tree,'requests')[1:]:
                if req[0] in ['sensitivity','slots-sensitive']:block(req[2],'ref-choices')[1].append([['slot-id',str(ident)],['choice-id','0']])
        spec['empty_changed_set_rule']='If a same-history differing row changes no slots, every declared singleton is minimal; no such row occurs in these seeds.'
    elif axis=='source-declarations':
        for req in block(tree,'requests')[1:]:
            if req[0]=='impact':inert_source(req[2],level);inert_source(req[3],level)
        for g in spec['graphs']:
            g['names'].extend(f'p8-inert-{i}-root' for i in range(level))
            g.setdefault('grounded_labels',{}).update({f'p8-inert-{i}-root':'justified' for i in range(level)})
        spec['added_argument_groups']=level;spec['added_ast_declarations_per_endpoint']=2*level
        spec['source_axis_level_unit']='fresh leaf-root groups per endpoint'
        spec['source_axis_approval']='protocol.json amendments/source-axis-groups: explicit researcher clarification before freeze; each group is one leaf plus one root argument'
    elif axis=='assumption-literals':
        for i in range(level):block(tree,'assumption-catalog').append(literal('slot-ne',2000+i,0))
        spec['unused_slot_rule']='All added fresh undeclared inequalities evaluate true, because selectionFor has no choice. These are table predicates, not evidence.'
    elif axis=='repeated-requests':
        original=deepcopy(block(tree,'requests')[1:]);requests=[]
        for i in range(level):
            for req in original:
                item=deepcopy(req)
                if i:item[1]=f'{item[1]}-repeat-{i+1}'
                requests.append(item)
        block(tree,'requests')[:]=['requests']+requests
    return tree,spec

def cert_path(case):return SUITE/'certificates'/(case+'.sexp')

def attach_certificate(case,tree,spec,producer=None):
    """Retain sanctioned producer syntax, validated against authored reports."""
    import subprocess
    import tempfile
    path=cert_path(case)
    if producer:
        one=deepcopy(tree);block(one,'requests')[:]=['requests',deepcopy(block(tree,'requests')[1])]
        with tempfile.TemporaryDirectory(prefix='p8-certificate-') as temp:
            input_path=Path(temp)/'input.sexp';input_path.write_bytes(canonical(one))
            captured=subprocess.run([str(producer),str(input_path)],check=True,capture_output=True)
        path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(captured.stdout)
    certificate=parse(path.read_bytes())
    req=block(tree,'requests')[1]
    assert certificate[1:3]==req[2:4],f'{case}: stale certificate endpoints'
    for i in range(2):
        expected=spec['rejections'][i]
        assert certificate[8+i][2]==([] if expected is None else [expected]),f'{case}: rejection specification disagrees with producer syntax'
        assert certificate[8+i][1]==boolatom(spec['statuses'][i] is not None)
    # The producer's answer is NOT copied to expected. The checks are reviewed
    # specification constraints on a supplied certificate before driver run.
    block(tree,'requests').append(['verify-impact','verify-endpoints',deepcopy(req[2]),deepcopy(req[3]),certificate])
    spec['certificate_provenance']={'purpose':'sanctioned API syntax producer; independently annotated report and query expectations','helper':'scripts/inquiry-impact-producer.hs','helper_sha256':sha((ROOT/'scripts/inquiry-impact-producer.hs').read_bytes()),'artifact_path':str(path.relative_to(SUITE)),'artifact_sha256':sha(path.read_bytes()),'api':'Lara.Process.Impact.impactCertificate . compareEndpoints . observeEndpoint','used_as_semantic_oracle':False}
    spec['exact_rejection_runtime_evidence']='Successful verify-impact checks supplied endpoint-report rejection against the exact endpoints; impact-result itself has no rejection field.'
    return tree,spec

def results_for(tree,spec):
    if spec['kind']=='family':return family_bodies(tree,spec)
    results=[]
    for req in block(tree,'requests')[1:]:
        if req[0]=='impact':body=spec['expected_body']
        else:body=['verification-body',['invalid-certificate',['false-read-evidence']]] if req[1]=='tampered' else ['verification-body',['verified']]
        results.append(['inquiry-result','1',req[1],deepcopy(body)])
    return results

def counters_for(tree,spec,data):
    histories=spec.get('histories',[[]]);rows=spec.get('rows',[{'choices':[]} for _ in histories]);steps=spec.get('history_search_steps',1)
    endpoints=[source for req in block(tree,'requests')[1:] if req[0] in ['impact','verify-impact'] for source in req[2:4]]
    catalog=block(tree,'assumption-catalog')[1:];distinct=[]
    for x in catalog:
        if x in distinct:distinct.remove(x)
        distinct.append(x)
    subsets=2**len(distinct);pairs=0
    for req in block(tree,'requests')[1:]:
        if req[0] in ['impact','verify-impact']:
            # Read inventory follows the approved small annotated carrier/region,
            # not certificate producer output: 5 global + 3 query + support +
            # one attack key for every carrier x ancestry member.
            inventory=spec.get('request_graphs',{}).get(req[1],spec['graphs'])
            pairs+=2+sum(8+len(g['query_support'])+len(g['names'])*len(g['query_ancestry']) for g in inventory)
        elif req[0]=='minimal-assumptions':
            pairs+=sum(sum(all(table_holds(distinct[j],r) for j in ids) for r in rows) for n in range(len(distinct)+1) for ids in itertools.combinations(range(len(distinct)),n))
        else:pairs+=len(rows)
    declarations=0
    for r in rows:
        declarations+=len(program(tree[3])[6])-1
        for sid,cid in r['choices']:
            declared=next(s for s in block(tree,'slots')[1:] if s[1][1]==str(sid));choice=next(c for c in declared[2] if c[1][1]==str(cid));declarations+=len(decode_datum(choice[3][2]))-1
    declarations+=sum(len(program(s)[6])-1 for s in endpoints)
    extensions=0
    if not spec.get('guard_survival'):
        # Every seed slot guard is truth. A declared singleton contributes one
        # logical node per surviving product prefix, even though it adds no row.
        for _ in histories:
            prefix=1
            for s in block(tree,'slots')[1:]:prefix*=len(s[2]);extensions+=prefix
    else:extensions=sum(len(v['choices']) for v in spec['guard_survival'])
    return {'histories':len(histories),'sources':len(rows)+len(endpoints),'source-bytes':len(data),'declarations':declarations,'search-steps':steps+extensions,'pairs':pairs,'subsets':sum(subsets for req in block(tree,'requests')[1:] if req[0]=='minimal-assumptions')}

def t16(seed):
    tree,spec=deepcopy(seed);cert=deepcopy(block(tree,'requests')[2][4]);block(tree,'requests')[:]=['requests',['verify-impact','original',deepcopy(cert[1]),deepcopy(cert[2]),deepcopy(cert)]]
    read=next(r for r in cert[20] if r[2][0]=='k-blocked-query');assert read[3][0]=='v-bool';old=read[3][1];read[3][1]='true' if old=='false' else 'false'
    block(tree,'requests').append(['verify-impact','tampered',deepcopy(cert[1]),deepcopy(cert[2]),cert])
    spec['tamper']={'key':read[2],'old_value':['v-bool',old],'new_value':read[3],'same_ReadKey_Val_type':True,'expected_fault':'false-read-evidence'}
    spec['specification']='Identity accepted endpoints: original certificate verifies. Alter only recorded BlockedQuery boolean value at same key, keeping all other certificate fields; exact fault false-read-evidence.'
    return tree,spec

def control_expected(name):return [parse(line) for line in (FIXTURES/(name+'.expected')).read_bytes().splitlines() if line]

def control_spec(name,tree):
    # Existing development goldens are disclosed, never upgraded to independent
    # semantic evidence. Construction counters use finite authored inventories.
    hcount=0 if name=='inconsistent' else 2 if name in ['blocked-conditional','impact-rejected'] else 1
    hsteps=35 if name=='inconsistent' else 9 if name in ['blocked-conditional','impact-rejected'] else 14 if name in ['fixed-witness','hypothetical-audit','forged-observed'] else 1
    assignments=[list(zip([int(s[1][1]) for s in block(tree,'slots')[1:]],choices)) for choices in itertools.product(*[[int(c[1][1]) for c in s[2]] for s in block(tree,'slots')[1:]])]
    spec={'kind':'development-control','histories':[[] for _ in range(hcount)],'history_search_steps':hsteps,'rows':[{'choices':a} for _ in range(hcount) for a in assignments]}
    # Family-only controls need no graph computation. Endpoint controls have
    # finite carrier and query ancestry inventories fixed by source construction.
    specs={'new-attacker':[(2,1,1),(3,2,1)],'shared-discharge':[(2,1,1),(3,3,1)],'unrelated-self-attack':[(3,2,1),(4,2,1)],'blocked-conditional':[(2,2,1),(3,3,1)],'verified-certificate':[(3,3,1),(2,2,1)],'tampered-certificate':[(3,3,1),(2,2,1)]}
    if name in specs:spec['graphs']=[graph([f'n{i}' for i in range(n)],[],[f'n{i}' for i in range(r)],['q']*q) for n,r,q in specs[name]]
    return spec

REVIEW={'status':'pending-independent-review','author':'Codex case author','author_provenance':'ai-executed','reviewer':None,'driver_output_used':False,'analysis_implementation_imported':False,'specification_references':['docs/theory-process.md#what-do-the-exact-inquiry-analyses-compute','docs/theory-process.md#how-is-an-edits-impact-certified','docs/theory-process.md#what-does-the-inquiry-wrapper-add']}

def semantic_digest(oracle):
    content={'expected':oracle['expected'],'semantic_specification':oracle['semantic_specification']}
    return sha((json.dumps(content,sort_keys=True,separators=(',',':'),ensure_ascii=False)+'\n').encode('utf-8'))

def review_matches(prior,entry,oracle,data,ancestry):
    """A review binds input bytes and ancestry as well as semantic annotation."""
    if not entry or entry.get('input_sha256')!=sha(data) or js(entry.get('source_ancestry'))!=js(ancestry):return False
    if prior.get('expected')!=oracle['expected'] or js(prior.get('semantic_specification'))!=js(oracle['semantic_specification']):return False
    provenance=prior.get('review_provenance',{})
    if provenance!=entry.get('review_provenance'):return False
    for key in ['reviewed_input_sha256','input_sha256']:
        if key in provenance and provenance[key]!=sha(data):return False
    for key in ['semantic_content_sha256','reviewed_semantic_content_sha256']:
        if key in provenance and provenance[key]!=semantic_digest(oracle):return False
    return True

def differences(outputs):
    return [str(path.relative_to(SUITE)) for path,data in outputs.items() if not path.exists() or path.read_bytes()!=data]


def materialize(producer=None):
    manifest=json.loads((SUITE/'MANIFEST.json').read_text());outputs={};entries=[]
    frozen=manifest.get('state')=='frozen'
    if manifest['recipe_version'] != RECIPE_VERSION:raise SystemExit('recipe version does not match manifest')
    if frozen and producer is not None:raise SystemExit('frozen suite refuses certificate producer; no artifacts changed')
    candidate_review=False
    if RECIPE_VERSION == CORRECTED_RECIPE:
        item=manifest.get('independent_review',{});receipt_path=SUITE/item.get('path','independent-review.json')
        if receipt_path.is_file() and item.get('sha256')==sha(receipt_path.read_bytes()):
            receipt=json.loads(receipt_path.read_text())
            candidate_review=(receipt.get('status')=='PASS' and
                receipt.get('reviewed_author_generator_sha256')==sha(Path(__file__).read_bytes()) and
                receipt.get('driver_outputs_used') is False and receipt.get('analysis_implementation_imported') is False)
    prior_entries={e['case_id']:e for e in manifest.get('cases',[])}
    def add(name,data,tree,spec,stratum,ancestry,expected=None):
        if RECIPE_VERSION == CORRECTED_RECIPE and (name=='T07' or name.startswith('T07-source-declarations-')):
            from inquiry_support_annotations import t07_annotations, validate_ground_annotations
            groups=spec.get('added_argument_groups',0)
            terms=[t07_annotations(groups,False),t07_annotations(groups,True)]
            req=block(tree,'requests')[1]
            keys=[validate_ground_annotations(program(source),policy(source),annotation) for source,annotation in zip(req[2:4],terms)]
            spec['ground_support_annotations']={'scope':'bounded parameter-free construction; pending independent review','terms':terms,'keys':keys}
            spec['specification']='Two distinct rule identities r-s and r-s-new share the seed premise and s conclusion. Their complete ground support terms differ. Both unattacked attackers defeat witness and propagate to consumer. Witness stays defeated; ancestry changes and locality fails.'
        expected=results_for(tree,spec) if expected is None else expected
        oracle={'schema':'inquiry-p8-oracle','schema_version':1,'case_id':name,'oracle_kind':'existing-conformance-golden' if stratum=='development_controls' else 'independent-finite-semantic-annotation','expected':{'result_kind':'results','exit_code':0,'results':expected},'semantic_specification':spec,'review_provenance':deepcopy(REVIEW)}
        if stratum=='development_controls':oracle['review_provenance']['status']='disclosed-development-control';oracle['development_provenance']=ancestry
        prior_path=SUITE/'oracles'/(name+'.json')
        if prior_path.exists():
            prior=json.loads(prior_path.read_text())
            # Preserve only a review bound to this corrected author source, then
            # require exact input/ancestry/meaning correspondence as before.
            # The frozen manifest loader also validates every review receipt.
            fresh_review=(candidate_review and prior.get('review_provenance',{}).get('review_sha256')==manifest['independent_review']['sha256'])
            if (RECIPE_VERSION != CORRECTED_RECIPE or fresh_review) and review_matches(prior,prior_entries.get(name),oracle,data,ancestry):
                oracle['review_provenance']=prior['review_provenance']
        ipath='inputs/'+name+'.sexp';opath='oracles/'+name+'.json';odata=js(oracle);outputs[SUITE/ipath]=data;outputs[SUITE/opath]=odata
        reqs=block(tree,'requests')[1:];query_order=[r[1] for r in block(tree[2],'queries')[1:]]+[r[1] for r in reqs];limits={x[0]:min(int(x[1]),{'histories':10000,'sources':10000,'source-bytes':1048576,'declarations':10000,'search-steps':200000,'pairs':4096,'subsets':4096}[x[0]]) for x in block(tree,'inquiry-limits')[1:]};limits['histories']=min(limits['histories'],int(block(block(tree[2],'limits'),'completions')[1]))
        limits['embedded-events']=min(8,int(block(block(tree[2],'limits'),'events')[1]))
        event_inventory=[x[:3] for x in block(tree[2],'record')[1:] if x[0]=='event']+block(tree[2],'universe')[1:]
        embedded_event_count=len({wire(x) for x in event_inventory})
        counters=counters_for(tree,spec,data)
        entries.append({'case_id':name,'stratum':stratum,'classification':'development-control' if stratum=='development_controls' else 'authored-control' if stratum=='authored_controls' else 'generated-size-variant','source_ancestry':ancestry,'input_path':ipath,'input_sha256':sha(data),'oracle_path':opath,'oracle_sha256':sha(odata),'query_order':query_order,'expected_embedded_event_count':embedded_event_count,'reference':[r[2] for r in reqs if r[0] in ['sensitivity','slots-sensitive']] or None,'catalog':block(tree,'assumption-catalog')[1:],'effective_declared_limits':limits,'expected_counters':{'basis':'expected finite construction, not runtime telemetry','values':counters},'expected_result_kind':'results','review_provenance':oracle['review_provenance']})
        if RECIPE_VERSION == CORRECTED_RECIPE:entries[-1]['authored_semantic_content_sha256']=semantic_digest(oracle)
    for item in manifest['legacy_controls']:
        name=item['case_id'];data=(ROOT/item['input_path']).read_bytes();tree=parse(data);assert sha(data)==item['input_sha256'];assert sha((ROOT/item['golden_path']).read_bytes())==item['golden_sha256']
        spec=control_spec(name,tree)
        # Catalog control truth table uses its exact approved binary assignments.
        if name=='minimal-conditions':
            for row in spec['rows']:row['history']=[]
        if name=='impact-rejected':
            # First pair has rejected/accepted carriers; second both rejected.
            spec['graphs']=[deepcopy(G_REJECT),deepcopy(G_PLAIN)]
            spec['request_graphs']={'dup-plain':spec['graphs'],'reject-dup':[deepcopy(G_REJECT),deepcopy(G_REJECT)]}
        add(name,data,tree,spec,'development_controls',deepcopy(item),control_expected(name))
    seeds=authored()
    for name in ['T01','T02','T03','T04','T08']:seeds[name]=attach_certificate(name,*seeds[name],producer)
    seeds['T08'][1]['certificate_correspondence']={'before_raw_names':['witness','consumer','attacker'],'after_raw_names':['attacker','witness','consumer'],'before_support_raw_indices':[0],'after_support_raw_indices':[1],'support_identity':'witness','stable_carrier':['attacker','witness','consumer'],'node_difference':[],'edge_difference':[],'ancestry_identities':['witness','attacker'],'incoming_by_identity':{'witness':['attacker'],'attacker':[]},'equal_blocking':True}
    seeds['T16']=t16(seeds['T01'])
    ancestry_controls={'T01':'impact-rejected','T02':'impact-rejected','T03':'impact-rejected','T04':'impact-rejected','T05':'blocked-conditional','T06':'unrelated-self-attack','T07':'unrelated-self-attack','T08':'unrelated-self-attack','T09':'impact-rejected','T10':'fixed-witness','T11':'reference-sensitivity','T12':'joint-only','T13':'impact-rejected','T14':'impact-rejected','T15':'fixed-witness','T16':'impact-rejected'}
    for name,(tree,spec) in seeds.items():
        source=ancestry_controls[name];ancestry={'recipe':name,'code_commit':manifest['code_commit'],'vocabulary_source_path':'fixtures/process/inquiry/'+source+'.sexp','vocabulary_source_sha256':sha((FIXTURES/(source+'.sexp')).read_bytes()),'construction':'structural extraction and approved authored edits; no final driver outputs'}
        add(name,canonical(tree),tree,spec,'authored_controls',ancestry)
    for axis,levels,names in AXES:
        for seed in names:
            for level in levels:
                name=f'{seed}-{axis}-{level}';tree,spec=vary(*seeds[seed],axis,level)
                if axis=='source-declarations' and seed=='T01' and level:
                    block(tree,'requests')[:]=['requests',block(tree,'requests')[1]];tree,spec=attach_certificate(name,tree,spec,producer)
                add(name,canonical(tree),tree,spec,'generated_variants',{'seed':seed,'axis':axis,'level':level,'recipe_version':manifest['recipe_version']})
    groups={}
    for entry in entries:groups.setdefault(entry['input_sha256'],[]).append(entry['case_id'])
    manifest['cases']=entries;manifest['duplicate_content_groups']=[{'input_sha256':h,'case_ids':ids} for h,ids in groups.items() if len(ids)>1];manifest['unique_input_count']=len(groups)
    if manifest['state'] not in ('frozen','awaiting-researcher-approval'):manifest['state']='awaiting-independent-review'
    assert len(entries)==96
    assert [sum(e['stratum']==s for e in entries) for s in ['development_controls','authored_controls','generated_variants']]==[16,16,64]
    for e in entries:
        assert len(e['query_order'])==len(set(e['query_order'])),e['case_id']
    outputs[SUITE/'MANIFEST.json']=js(manifest)
    changed=differences(outputs) if frozen else []
    if changed:raise SystemExit('frozen suite differs; no artifacts changed: '+', '.join(changed))
    return outputs

def main(argv=None):
    global SUITE, RECIPE_VERSION
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--suite',type=Path,default=SUITE,help='explicit additive suite path; original frozen suite stays read-only')
    parser.add_argument('--recipe-version',choices=['inquiry-p8-recipes@1',CORRECTED_RECIPE],default=RECIPE_VERSION)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--producer',type=Path,help='explicit sanctioned helper for producing/updating certificate syntax; never an inquiry driver')
    args=parser.parse_args(argv)
    SUITE=args.suite.resolve();RECIPE_VERSION=args.recipe_version
    if RECIPE_VERSION == CORRECTED_RECIPE and SUITE == (ROOT/'evaluation/inquiry-p8').resolve():parser.error('corrected recipe cannot target original suite')
    if args.check and args.producer:parser.error('--check is read-only; do not pass --producer')
    frozen=json.loads((SUITE/'MANIFEST.json').read_text()).get('state')=='frozen'
    outputs=materialize(args.producer)
    changed=differences(outputs)
    if args.check and changed:raise SystemExit('generated bytes differ: '+', '.join(changed))
    # A frozen suite is read-only in both CLI modes, even if every byte matches.
    if not args.check and not frozen:
        for path,data in outputs.items():
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes(data)
    verb='checked' if args.check or frozen else 'authored'
    print(f'{verb} 96 P8 cases; independent review required before freeze')
if __name__=='__main__':main()
