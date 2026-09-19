"""Finite-difference check that the tree formulas of Section 3 solve the primitive equation (2.48).

Compares the boundary convention Theta_{t m_i m_{i+1}} at a_i (A, Definition 3.3 item 1) with
Theta_{t m_{i-1} m_i} (B, the n = 4 display after Figure 6), at n = 3, 4, and the star value
Theta^2 with Theta at n = 2.  The cut-and-glue operators follow RBM1D/Loop/Index.lean.
Pure Python, no dependencies:  python3 scripts/tree_ode_check.py
"""
import cmath, itertools
L=5
def inv(M):
    n=len(M); A=[row[:]+[complex(i==j) for j in range(n)] for i,row in enumerate(M)]
    for c in range(n):
        p=max(range(c,n),key=lambda r:abs(A[r][c])); A[c],A[p]=A[p],A[c]
        pv=A[c][c]; A[c]=[x/pv for x in A[c]]
        for r in range(n):
            if r!=c:
                f=A[r][c]; A[r]=[a-f*b for a,b in zip(A[r],A[c])]
    return [row[n:] for row in A]
S=[[1/3 if min((i-j)%L,(j-i)%L)<=1 else 0 for j in range(L)] for i in range(L)]
def Theta(xi): return inv([[complex(i==j)-xi*S[i][j] for j in range(L)] for i in range(L)])
m0=cmath.exp(1.1j)
def m(s): return m0 if s else m0.conjugate()
W=1.0
# Lean conventions: 1-based k,l
def cutL(k,l,b,sig,a): return (sig[:k]+sig[l-1:], a[:k-1]+[b]+a[l-1:])
def cutR(k,l,b,sig,a): return (sig[k-1:][:l-k+1], a[k-1:][:l-k]+[b])
def K2(t,sig,a):
    mu=m(sig[0])*m(sig[1]); return mu/W*Theta(t*mu)[a[0]][a[1]]
def K3(t,sig,a,conv):
    n=3; ms=[m(s) for s in sig]; tot=0
    Th={}
    for b in range(L):
        p=1
        for i in range(n):
            if conv=='A': mu=ms[i]*ms[(i+1)%n]      # a_i between R_i,R_{i+1}
            else: mu=ms[(i-1)%n]*ms[i]              # n=4 display convention
            if mu not in Th: Th[mu]=Theta(t*mu)
            p*=Th[mu][a[i]][b]
        tot+=p
    return ms[0]*ms[1]*ms[2]/W**2*tot
def K(t,sig,a,conv):
    return K2(t,sig,a) if len(a)==2 else K3(t,sig,a,conv)
def rhs(t,sig,a,conv):
    n=len(a); tot=0
    for k in range(1,n+1):
        for l in range(k+1,n+1):
            for x in range(L):
                for y in range(L):
                    if S[x][y]==0: continue
                    s1,a1=cutL(k,l,x,sig,a); s2,a2=cutR(k,l,y,sig,a)
                    tot+=K(t,s1,a1,conv)*S[x][y]*K(t,s2,a2,conv)
    return W*tot
t=0.4; h=1e-5
for sig in [(True,True,False),(True,False,False),(True,False,True)]:
  for a in [[0,1,3],[2,2,4]]:
    for conv in 'AB':
        d=(K(t+h,list(sig),a,conv)-K(t-h,list(sig),a,conv))/(2*h)
        r=rhs(t,list(sig),a,conv)
        print(sig,a,conv,'|d-rhs|=%.2e'%abs(d-r),'|d|=%.3f'%abs(d))
# n=2 check: star formula (Theta^2) vs Theta
sig=[True,False]; a=[0,2]
mu=m(True)*m(False)
star=lambda t: mu/W*sum(Theta(t*mu)[a[0]][b]*Theta(t*mu)[a[1]][b] for b in range(L))
d=(star(t+h)-star(t-h))/(2*h); r=rhs(t,sig,a,'A')
print('n=2 star Theta^2: |d-rhs|=%.2e'%abs(d-r))
d=(K2(t+h,sig,a)-K2(t-h,sig,a))/(2*h); print('n=2 Theta: |d-rhs|=%.2e'%abs(d-r))
# initial values
print('K3 at t=0 conv A',K3(0,[True,True,False],[1,1,1],'A'), 'expected', m(True)*m(True)*m(False))

def K4(t,sig,a,conv):
    ms=[m(s) for s in sig]; n=4
    def Th(mu): return Theta(t*mu)
    if conv=='A': bd=[Th(ms[i]*ms[(i+1)%4]) for i in range(4)]
    else: bd=[Th(ms[(i-1)%4]*ms[i]) for i in range(4)]
    T13=Th(ms[0]*ms[2]); T24=Th(ms[1]*ms[3])
    I=lambda x,y: 1.0 if x==y else 0.0
    tot=0
    for b in itertools.product(range(L),repeat=4):
        p=1
        for i in range(4): p*=bd[i][a[i]][b[i]]
        if p==0: continue
        c=0
        if b[0]==b[1]==b[2]==b[3]: c+=1
        if b[0]==b[1] and b[2]==b[3]: c+=T13[b[0]][b[2]]-I(b[0],b[2])
        if b[0]==b[3] and b[1]==b[2]: c+=T24[b[0]][b[1]]-I(b[0],b[1])
        tot+=p*c
    return ms[0]*ms[1]*ms[2]*ms[3]/W**3*tot
def K(t,sig,a,conv):
    return {2:K2,3:lambda t,s,a: K3(t,s,a,conv),4:lambda t,s,a: K4(t,s,a,conv)}[len(a)](t,sig,a) if len(a)==2 else {3:K3,4:K4}[len(a)](t,sig,a,conv)
print('--- n=4 ---')
for sig in [(True,True,False,False),(True,False,True,True)]:
  for a in [[0,1,3,2]]:
    for conv in 'AB':
        d=(K(t+h,list(sig),a,conv)-K(t-h,list(sig),a,conv))/(2*h)
        r=rhs(t,list(sig),a,conv)
        print(sig,a,conv,'|d-rhs|=%.2e'%abs(d-r),'|d|=%.3f'%abs(d))
