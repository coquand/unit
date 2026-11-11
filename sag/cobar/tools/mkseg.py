import re
def base_fields(path='CBase.seg'):
    t=open(path).read()
    i=t.index('module CB {'); body=t[i+len('module CB {'):]
    j=body.index('\n  import '); body=body[:j]
    src='\n'.join(re.sub(r'--.*','',l) for l in body.split('\n'))
    stmts=[];cur='';d=0
    for ch in src:
        cur+=ch
        if ch in '{([': d+=1
        elif ch in '})]': d-=1
        elif ch==';' and d==0:
            stmts.append(cur.strip()); cur=''
    out=[];names=[]
    for s in stmts:
        if not s or s.startswith('open ') or s.startswith('module '): continue
        nm=re.match(r"[A-Za-z0-9'\-]+",s).group(0)
        d=0;eq=False
        for k,ch in enumerate(s):
            if ch in '{([': d+=1
            elif ch in '})]': d-=1
            elif ch=='=' and d==0 and s[k-1]==' ' and s[k+1:k+2] in (' ','\n'): eq=True;break
        if eq:
            if nm in ('IvP','PhiL','HoldsL'): out.append(('def',nm,s))
            continue
        out.append(('field',nm,s)); names.append(nm)
    return out,names

MEM="FibClL FibCwF PosId PosJNat PosIdY PosIdYFib PosIdYJ FibIdRd FibIdCen FibId FibNF CLocBoundContr CLocBoundRetr FibContr FibHt FibYC FibC2 FibS3".split()
# the truncation layer (SAG 8.3 normal forms, pushforward, fibrancy, packaging)
TRUNC="CTruncRaw CTruncCode CTruncGood CTruncLaws CTruncType CTruncExt CTruncNat CTruncAlg CTruncGraph CTruncGraphNat CTruncRec CTruncRecExt CTrunc CTruncSeeded CTruncIsProp CTruncFinal CTruncEmpty CTruncEta CTruncHom CTruncUnique CTruncMorphism CTruncSection CTruncInd CTruncTransport CTruncSeededBack CTruncLift CTruncElim CTruncHProp CTruncFromProp CTruncElimProp CTruncPush CTruncPushAlg CTruncSubOp CTruncPushAdj CTruncSeed CTruncFib CTruncCwF".split()
MEM=MEM+TRUNC
def gen(name):
    import ivrw
    t=open(name+'.seg').read()
    t=re.sub(r'^level a l ;','level l ;',t,flags=re.M)
    t=re.sub(r'^level a ; *constraint a <= l ;[^\n]*\n','',t,flags=re.M)
    t=t.replace('open Trees[a] ; open Arith[a] ; open Cat[a] ;','open Trees[a] ; open Arith[a] ;')
    for pat in [r'^open Cat\[a\] ;[^\n]*\n', r'^open SmallCat\[a\]\.Objs\[obV\] ; open SmallCat\[a\]\.Homs\[obV, homV\] ;[^\n]*\n', r'^open CPosC\[a\] ;[^\n]*\n', r'^open CPosBase\[a\] ;[^\n]*\n', r'^open PosCofConj\[a\] ;[^\n]*\n']:
        t=re.sub(pat,'',t,flags=re.M)
    t=t.replace('open Trees[a] ; open Arith[a] ; open Cat[a] ;','open Trees[a] ; open Arith[a] ;')
    t=re.sub(r'module PB = (PosFull|CPosInst)\[a\]\.PB ; ?','',t)
    for m in MEM:
        t=re.sub(r"(?<![A-Za-z0-9'._\-])"+m+r"\[a, ?l\]",'G'+m+'[l]',t)
        t=re.sub(r"(?<![A-Za-z0-9'._\-])"+m+r"\[a,l\]",'G'+m+'[l]',t)
    t=re.sub(r"(?<![A-Za-z0-9'._\-])El Iv(?![A-Za-z0-9'_\-])",'IPt',t)
    t,n=ivrw.rewrite(t)
    t,n2=ivrw.rewrite(t)
    t=re.sub(r"([A-Za-z0-9]+\.)piH ([A-Za-z0-9'.]+) Iv(?![A-Za-z0-9'_\-])",r'\1piI \2',t)
    if name=='CLocBoundContr': t=fixLBC(t)
    if name=='CTruncIsProp': t=fixLBC(t)
    if name in ('CTruncPush','CTruncType','CTruncPushAdj'):
        # local variables e0 / e1 clash with the segment's fields
        for a_,b_ in [('e0','eq0'),('e1','eq1')]:
            t=re.sub(r"(?<![A-Za-z0-9'._\-])"+a_+r"(?![A-Za-z0-9'_\-])",b_,t)
    t=applyPatches(name,t)
    if name=='CLocBoundRetr': t=fixLBR(t)
    t=t.replace('dconjC','dconj').replace('dc-inC','dc-in').replace('dc-outC','dc-out')
    return t
def fixLBR(t):
    def sub(old,new,c=1):
        nonlocal t
        assert t.count(old)==c,(old,t.count(old)); t=t.replace(old,new)
    sub("(\\ Z g i j -> apH (onE Z) (PA.pv-irr X x s Z (compH Z Y X h g) i j)) ;","(\\ Z g i j -> apH (onE Z) (PA.pv-irr X x s Z (compH Z Y X h g) (PB.lands-pre Z Y X h s.pQ g i) (PB.lands-pre Z Y X h s.pQ g j))) ;")
    sub("    vp (Z : Ob) (f : Hom Z Y) (i j : PB.Lands Z X s.pQ (compH Z Y X h f))","    vp (Z : Ob) (f : Hom Z Y) (i : PB.Lands Z X s.pQ (compH Z Y X h f)) (j : PB.Lands Z Y (PB.pre Y X h s.pQ) f)")
    sub("(P.pv-irr X x s Z (compH Z Y X h f) i j))","(P.pv-irr X x s Z (compH Z Y X h f) i (PB.lands-pre Z Y X h s.pQ f j)))")
    sub("(EK.PT.rside Y X h P0.w P0.LS.side) P1.LS.side (refl (PB.pre Y X h s.pQ)) vp ;","(EK.PT.rside Y X h P0.w P0.LS.side) P1.LS.side (refl (PB.pre Y X h s.pQ))\n        (\\ Z f i0 j -> vp Z f (PB.lands-pre Z Y X h s.pQ f i0) j) ;")
    return t

def applyPatches(name,t):
    # patches.json: per file, [old, new, count]: uses of lands-pre / pre-lands where the
    # poset files use that landing in a restricted sieve is landing of the composite
    import json,os
    db=json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'patches.json')))
    for old,new,c in db.get(name,[]):
        assert t.count(old)==c,(name,old[:60],t.count(old)); t=t.replace(old,new)
    return t
def fixLBC(t):
    def sub(old,new,c=1):
        nonlocal t
        assert t.count(old)==c,(old,t.count(old)); t=t.replace(old,new)
    sub("PB.pre X Iv j (CPosInst[a].ptSO (endpoint n))","PB.endS X j (endpoint n)")
    sub("(CPosInst[a].pt-disjO Y (ivA Y X h j) i i')","(PB.pt-disj Y (ivA Y X h j) (PB.lands-endS Y X j e0 h i) (PB.lands-endS Y X j e1 h i'))")
    sub("(CPosInst[a].pt-disjO Y (ivA Y X h j) i' i)","(PB.pt-disj Y (ivA Y X h j) (PB.lands-endS Y X j e0 h i') (PB.lands-endS Y X j e1 h i))")
    sub("PB.pre-comp Y X Iv h j (CPosInst[a].ptSO (endpoint n))","PB.end-pre Y X h j (endpoint n)")
    i=t.index("        substH (\\ h -> PB.Lands X Iv (CPosInst[a].ptSO (endpoint q.1)) h)"); j=t.index(";",i)
    t=t[:i]+"        PB.pt-lands X (endpoint q.1) "+t[j:]
    sub("(P.rside Y X h z.1 E0.J.side) E1.J.side eQ ev ;","(P.rside Y X h z.1 E0.J.side) E1.J.side eQ\n        (\\ Z f i0 i' -> ev Z f (PB.lands-pre Z Y X h E0.J.side.pQ f i0) i') ;")
    return t

# usage (from sag/cobar): python3 tools/mkseg.py   -- regenerates G<Name>.seg
if __name__=='__main__':
    import sys,os
    sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
    for m in MEM:
        hdr='-- G%s.seg: GENERATED from %s.seg by tools/mkseg.py (canonicity-c2): the same file\n-- as a member of the segment CFibSeg.FB, over any base with the dependent\n-- conjunction of sieves.  Do not edit; change %s.seg or the generator.\n'%(m,m,m)
        open('G'+m+'.seg','w').write(hdr+gen(m))
