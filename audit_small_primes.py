from fractions import Fraction as F
from math import factorial
from random import Random


def mulroot(a,r):
    out=[F(0)]*(len(a)+1)
    for i,v in enumerate(a):
        out[i]-=r*v
        out[i+1]+=v
    return out


def quo(a,b):
    a=a[:]
    if len(a)<len(b): return [F(0)]
    out=[F(0)]*(len(a)-len(b)+1)
    while len(a)>=len(b):
        c=a[-1]/b[-1]
        i=len(a)-len(b)
        out[i]=c
        for j,v in enumerate(b): a[i+j]-=c*v
        a.pop()
    return out


def ev(a,x):
    y=F(0)
    for v in reversed(a): y=y*x+v
    return y


def vp(x,p):
    if not x:return 10**8
    a,b=x.numerator,x.denominator
    v=0
    while a%p==0:a//=p;v+=1
    while b%p==0:b//=p;v-=1
    return v


def ilog(a,p):
    v=0
    while p<=a:a//=p;v+=1
    return v

rng=Random(0)
count=0
for K in range(1,13):
    D=[F(1)]
    for r in range(-K,K+1):
        if r:D=mulroot(D,r)
    A=[F(1)]
    for d in range(71):
        P=quo([v*factorial(K)**2 for v in A],D)
        for p in [2,3,5,7,11,13]:
            L=ilog(2*K,p); M=max(L,ilog(max(1,d),p))
            bnd=-L-M
            for x in list(range(-K-2,K+3))+[rng.randrange(p**(L+M+2)) for _ in range(4)]:
                v=vp(ev(P,x),p)
                count+=1
                if v<bnd:
                    raise AssertionError((K,d,p,x,v,bnd))
        A=[v/F(d+1) for v in mulroot(A,d)]
print(f'No counterexample in {count} exact quotient evaluations (K=1..12, d=0..70).',flush=True)
