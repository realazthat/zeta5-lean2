#!/usr/bin/env python3
"""Exact directed fixed-point enclosure audit of Appendix A, Zenodo 22826419.
All interval arithmetic is integer arithmetic. This is independent audit code,
not a Lean proof and not a verification of Sections 3--5.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt
import re
from pathlib import Path
D=1<<192

def ceildiv(a,b): return -((-a)//b)
@dataclass(frozen=True)
class I:
    a:int
    b:int
    @staticmethod
    def rat(x):
        if isinstance(x,I): return x
        x=F(x); return I(x.numerator*D//x.denominator,ceildiv(x.numerator*D,x.denominator))
    def __add__(self,o):
        o=I.rat(o); return I(self.a+o.a,self.b+o.b)
    __radd__=__add__
    def __neg__(self): return I(-self.b,-self.a)
    def __sub__(self,o): return self+-I.rat(o)
    def __rsub__(self,o): return I.rat(o)+-self
    def __mul__(self,o):
        o=I.rat(o); vals=[self.a*o.a,self.a*o.b,self.b*o.a,self.b*o.b]
        return I(min(vals)//D,ceildiv(max(vals),D))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=I.rat(o); assert o.a>0 or o.b<0
        vals=[F(x*D,y) for x in (self.a,self.b) for y in (o.a,o.b)]
        lo=min(vals); hi=max(vals)
        return I(lo.numerator//lo.denominator,ceildiv(hi.numerator,hi.denominator))
    def __rtruediv__(self,o): return I.rat(o)/self
    def __pow__(self,n):
        assert n>=0
        v=I.rat(1)
        for _ in range(n): v=v*self
        return v
    def sqrt(self):
        assert self.a>=0
        lo=isqrt(self.a*D); hi=isqrt(self.b*D)
        return I(lo,hi+(hi*hi<self.b*D))
    def decimal(self): return f'[{self.a/D:.15f}, {self.b/D:.15f}]'

def log_reduced(r):
    z=(r-1)/(r+1); assert 0<=z.a and z.b*3<=D+10
    z2=z*z; power=z; s=I.rat(0)
    for k in range(64):
        s=s+power*F(2,2*k+1); power=power*z2
    rem=2*power/(129*(1-z2))
    return I(s.a,s.b+rem.b)
LOG2=log_reduced(I.rat(2))
def log_point(x):
    assert x>0
    e=x.bit_length()-193
    r=I.rat(F(x,D)*F(2)**(-e))
    assert r.a>=D and r.b<2*D+1
    return log_reduced(r)+e*LOG2

def log(x):
    x=I.rat(x); return I(log_point(x.a).a,log_point(x.b).b)

def atan_series(z):
    z=I.rat(z); assert 0<=z.a and 2*z.b<=D
    z2=z*z; power=z; s=I.rat(0)
    for k in range(80):
        s=s+power*F((-1)**k,2*k+1); power=power*z2
    rem=(power/161).b
    return I(s.a-rem,s.b+rem)
PI=16*atan_series(I.rat(F(1,5)))-4*atan_series(I.rat(F(1,239)))
def atan_small(x):
    z=x/(1+(1+x*x).sqrt())
    return 2*atan_series(z)
def atan_point(v):
    x=I(v,v); assert x.a>=0
    return atan_small(x) if x.b<=D else PI/2-atan_small(1/x)
def atan(x):
    x=I.rat(x); return I(atan_point(x.a).a,atan_point(x.b).b)

DATA=[
(3906748086,8992695531,10515596180),
(2312248264,15340997855,29471737793),
(1402286665,25730180724,42934365099),
(881725356,41909578246,58204231966),
(578197906,65851089563,69037621310),
(396324613,99481037884,78873099189),
(283911191,144325727458,84856120711),
(212206188,201105762729,88396082127),
(165097686,269345996903,88303382125),
(133347132,347089554156,85472321255),
(111522114,430806704415,78899184238),
(96349355,515561896511,70353471918),
(85815639,595448778546,58838976615),
(78667711,664241383483,44421321106),
(74129565,716160577112,30462865791),
(71741310,746637295669,5959622577)]
DATA=[tuple(F(x,10**12) for x in row) for row in DATA]
ALPHA=F(3,40); LAMBDA=F(37,40); QM=F(59205077,10**10); QP=F(59205079,10**10)

def potential(t):
    ans=I.rat(0)
    for a,b,c in DATA:
        if a<=t<=b: u=log((b-a)/4)
        else:
            absval=abs(t-(a+b)/2)
            u=log((I.rat(absval)+I.rat((t-a)*(t-b)).sqrt())/2)
        ans=ans+c*u
    return ans

def field(t):
    if t==0: return -12*ALPHA*log(ALPHA)-2+12*ALPHA
    y=I.rat(t).sqrt()
    return log(1+t)-6*ALPHA*log(t+ALPHA**2)-2+12*ALPHA+2*y*(PI+atan(1/y)-6*atan(ALPHA/y))

def fieldprime(t):
    y=I.rat(t).sqrt()
    return 2*(PI+atan(1/y)-6*atan(ALPHA/y))

vstar_parenthesis=PI+atan(1/I.rat(QP).sqrt())-6*atan(ALPHA/I.rat(QM).sqrt())
assert vstar_parenthesis.b < 0
vstar=log(1+QM)-6*ALPHA*log(QP+ALPHA**2)-2+12*ALPHA+2*I.rat(QP).sqrt()*vstar_parenthesis

def main():
    assert sum(c for a,b,c in DATA)==LAMBDA
    assert all(0<a<b<2 and b-a>F(1,225) and c>0 for a,b,c in DATA)
    assert all(DATA[i+1][0]<DATA[i][0]<DATA[i][1]<DATA[i+1][1] for i in range(15))
    assert fieldprime(QM).b<0 and fieldprime(QP).a>0
    print('Table 1: positive weights, mass 37/40, nesting, length lower bounds VERIFIED')
    print('Derivative brackets at q-,q+ VERIFIED')
    print('Vstar:',vstar.decimal())
    text=Path(__file__).with_name('paper.txt').read_text()
    table=text.split('Table 2: Intervals for the potential bound.')[1].split('For t ≥ 2,')[0]
    rows=[]
    for line in table.splitlines():
        m=re.match(r'^\s*(\d+)\s+(\d+)\s+(.+?)\s*$',line)
        if not m: continue
        j,d=int(m[1]),int(m[2]); ks=m[3]
        ks=re.sub(r'(\d+),\s*\.\s*\.\s*\.\s*,\s*(\d+)',lambda m: ' '.join(str(k) for k in range(int(m[1]),int(m[2])+1)),ks)
        for k in map(int,re.findall(r'\d+',ks)): rows.append((j,d,k))
    A=[F(0)]+[a for a,b,c in reversed(DATA)]+[QM,QP]+[b for a,b,c in DATA]+[F(2)]
    assert all(A[i]<A[i+1] for i in range(35))
    cells=[]
    for j,d,k in rows:
        l=A[j]+(A[j+1]-A[j])*F(k,2**d)
        r=A[j]+(A[j+1]-A[j])*F(k+1,2**d)
        cells.append((l,r,j,d,k))
    cells.sort()
    assert cells[0][0]==0 and cells[-1][1]==2
    assert all(cells[i][1]==cells[i+1][0] for i in range(len(cells)-1))
    cache={t:potential(t) for row in cells for t in row[:2]}
    worst=None
    for l,r,j,d,k in cells:
        u=I(max(cache[l].a,cache[r].a),max(cache[l].b,cache[r].b))
        v=field(r) if r<=QM else field(l) if l>=QP else vstar
        bound=2*u-v
        assert bound.b*10**6 < -6645002*D, (j,d,k,bound.decimal())
        if worst is None or bound.b>worst[0].b: worst=(bound,(j,d,k))
    print(f'Table 2: {len(cells)} cells partition [0,2] exactly; ALL ENCLOSURES VERIFIED')
    print('Largest B enclosure:',worst[0].decimal(),'at row',worst[1])
    energy=I.rat(0); s=F(0)
    for a,b,c in DATA:
        energy=energy+((s+c)**2-s**2)*log((b-a)/4); s+=c
    cstar=-2*LAMBDA+12*ALPHA*LAMBDA*(1-log(ALPHA))+3*LAMBDA**2-2*LAMBDA**2*log(2*LAMBDA)
    assert energy.a*10**12>-2126593445148*D and energy.b*10**12<-2126593445147*D
    assert cstar.a*10**12>2653035990340*D and cstar.b*10**12<2653035990341*D
    combined=-LAMBDA*F(1329,200)-energy+cstar
    assert combined.b*2_000_000 < -2733991*D
    print('Energy I(rho):',energy.decimal())
    print('Cstar:',cstar.decimal())
    print('Combined coefficient:',combined.decimal())
    print('A.10, and final coefficient <-2733991/2000000 VERIFIED')
if __name__=='__main__': main()
