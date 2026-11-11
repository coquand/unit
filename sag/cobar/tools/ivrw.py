import re,sys
IDC=r"A-Za-z0-9'._\-"
def atom(s,i):
    # parse one atom starting at i (skipping spaces/newlines); return (text,end)
    while i<len(s) and s[i] in ' \n\t': i+=1
    if i>=len(s): return None
    if s[i]=='(':
        d=0;j=i
        while j<len(s):
            if s[j]=='(':d+=1
            elif s[j]==')':
                d-=1
                if d==0: return (s[i:j+1],j+1)
            j+=1
        return None
    m=re.compile('['+IDC+']+').match(s,i)
    if not m: return None
    j=m.end()
    while j<len(s) and s[j]=='[':   # instance brackets
        d=0;k=j
        while k<len(s):
            if s[k]=='[':d+=1
            elif s[k]==']':
                d-=1
                if d==0: break
            k+=1
        j=k+1
        m2=re.compile(r'(\.['+IDC+']+)?').match(s,j); j=m2.end()
    return (s[i:j],j)
def atoms(s,i,n):
    out=[]
    for _ in range(n):
        r=atom(s,i)
        if r is None: return None
        out.append(r[0]); i=r[1]
    return out,i
def pts(a):
    m=re.fullmatch(r'\(\s*ptS\s+(.*)\)',a,re.S)
    return m.group(1).strip() if m else None
RULES=[
 ('pre-comp',5,lambda a: a[2]=='Iv' and pts(a[5-0-0]) is None and False),
]
def rewrite(s):
    out=[];i=0;n=0
    heads=sorted(['pre-comp','comp-assoc','comp-idr','compH','pre','Lands','Hom','piH'],key=len,reverse=True)
    pat=re.compile(r'(?<!['+IDC+'])('+'|'.join(re.escape(h) for h in heads)+r')(?!['+IDC+'])')
    while True:
        m=pat.search(s,i)
        if not m: out.append(s[i:]); break
        out.append(s[i:m.start()]); h=m.group(1); j=m.end(); rep=None
        def get(k):
            return atoms(s,j,k)
        if h=='pre-comp':
            r=get(6)
            if r and r[0][2]=='Iv' and pts(r[0][5]): a=r[0]; rep=('end-pre %s %s %s %s %s'%(a[0],a[1],a[3],a[4],pts(a[5])),r[1])
        elif h=='comp-assoc':
            r=get(7)
            if r and r[0][3]=='Iv': a=r[0]; rep=('ivA-comp %s %s %s %s %s %s'%(a[0],a[1],a[2],a[5],a[6],a[4]),r[1])
        elif h=='comp-idr':
            r=get(3)
            if r and r[0][1]=='Iv': a=r[0]; rep=('ivA-id %s %s'%(a[0],a[2]),r[1])
        elif h=='compH':
            r=get(5)
            if r and r[0][2]=='Iv': a=r[0]; rep=('ivA %s %s %s %s'%(a[0],a[1],rewrite(a[4])[0],rewrite(a[3])[0]),r[1])
        elif h=='pre':
            r=get(4)
            if r and r[0][1]=='Iv' and pts(r[0][3]): a=r[0]; rep=('endS %s %s %s'%(a[0],rewrite(a[2])[0],pts(a[3])),r[1])
        elif h=='Lands':
            r=get(4)
            if r and r[0][1]=='Iv' and pts(r[0][2]): a=r[0]; rep=('Lands %s %s (endS %s %s %s) (idH %s)'%(a[0],a[0],a[0],rewrite(a[3])[0],pts(a[2]),a[0]),r[1])
        elif h=='Hom':
            r=get(2)
            if r and r[0][1]=='Iv': rep=('IvP %s'%r[0][0],r[1])
        elif h=='piH':
            r=get(2)
            if r and r[0][1]=='Iv': rep=('piI %s'%r[0][0],r[1])
        if rep: out.append(rep[0]); i=rep[1]; n+=1
        else: out.append(h); i=j
    return ''.join(out),n
if __name__=='__main__':
    tot=0
    for f in sys.argv[1:]:
        t=open(f).read()
        # keep comments untouched: process line by line splitting at '--' is unsafe for multi-line atoms; comments rarely contain patterns with Iv atoms that matter
        new,n=rewrite(t)
        left=len(re.findall(r'(?<!['+IDC+'])Iv(?!['+IDC+'])',re.sub(r'--.*','',new)))
        if n or left: print('%-16s %3d rewrites, %2d Iv left'%(f,n,left))
        open(f,'w').write(new); tot+=n
    print('total',tot)
