#!/usr/bin/env python3
"""The text of Sz8/Galois/NodeData.lean: residue witnesses modulo 1000003 for the seven factors of the
reduced node polynomial, the factor-product chain, and the primitive node polynomial itself.

Inputs: data/f.json and certificate/results/discriminant.pkl (restore with scripts/restore_discriminant.py;
its digest is fixed by certificate/manifest.json). Needs python-flint. About 50 s."""
import json
import math
import pickle
import sys
from fractions import Fraction as F
from fractions import Fraction as Fr

import flint

from paths import DISCRIMINANT_PKL, F_JSON

sys.set_int_max_str_digits(10**8)


def load_disc():
    d = pickle.loads(DISCRIMINANT_PKL.read_bytes())
    D = flint.fmpq_poly([flint.fmpq(F(s).numerator, F(s).denominator) for s in d['D']])
    S = flint.fmpq_poly([flint.fmpq(F(s).numerator, F(s).denominator) for s in d['S']])
    c = flint.fmpq(F(d['c']).numerator, F(d['c']).denominator)
    return D, S, c, d['m']


def generate():
    p = 1000003
    N = flint.nmod_poly
    co = json.loads(F_JSON.read_text())['coefficients']
    L = 13**182
    Fint = [[0]*8 for _ in range(66)]
    for k,v in co.items():
        i,j = map(int,k.split(',')); x = Fr(v)
        Fint[i][j] = x.numerator * (L // x.denominator)
    Fbar = [[Fint[i][j] % p for j in range(8)] for i in range(66)]
    Gbar = [[(i+1)*Fint[i+1][j] % p for j in range(8)] for i in range(65)]
    D,S,c,m = load_disc()
    cos = S.coeffs(); Ld = 1
    for x in cos: Ld = Ld*int(x.q)//math.gcd(Ld,int(x.q))
    St = [int(x.p)*(Ld//int(x.q)) for x in cos]
    g0 = 0
    for v in St: g0 = math.gcd(g0, v)
    St = [v//g0 for v in St]
    Sbar = N([v % p for v in St], p)
    fac = sorted([f for f,e in Sbar.factor()[1]], key=lambda f: f.degree())
    lcS = St[-1] % p
    assert N([lcS],p) * fac[0]*fac[1]*fac[2]*fac[3]*fac[4]*fac[5]*fac[6] == Sbar
    WT=313; SB=64
    def pack(poly2, wt=WT):
        n = 0
        for k in reversed(range(len(poly2))):
            v = 0
            for j in reversed(range(len(poly2[k]))):
                v = (v << SB) | poly2[k][j]
            n = (n << (SB*wt)) | v
        return n
    def unpack(n, nx, wt=WT):
        out=[]; mask=(1<<SB)-1
        for k in range(nx):
            row=[]
            for j in range(wt): row.append(n & mask); n >>= SB
            out.append(row)
        assert n == 0
        return out
    def strip(a):
        while a and a[-1] == 0: a.pop()
        return a
    lits = {}
    for idx, P in enumerate(fac):
        def red(a): return a % P
        def inv(a):
            g, s, t = a.xgcd(P); assert g.degree()==0
            return red(s * N([pow(int(g[0]), p-2, p)], p))
        fK = [red(N(Fbar[i], p)) for i in range(66)]
        gK = [red(N(Gbar[i], p)) for i in range(65)]
        def pdivmod(a, b):
            a = list(a); q = [N([],p)]*(max(len(a)-len(b)+1,0)); ib = inv(b[-1])
            while len(a) >= len(b):
                cq = red(a[-1]*ib); sh = len(a)-len(b); q[sh] = cq
                for i in range(len(b)): a[sh+i] = red(a[sh+i] - cq*b[i])
                a.pop()
            return q, strip(a)
        def pmul(a,b):
            out=[N([],p)]*(len(a)+len(b)-1)
            for i,x in enumerate(a):
                for j,y in enumerate(b): out[i+j]=red(out[i+j]+x*y)
            return out
        def padd(a,b):
            n=max(len(a),len(b)); return [red((a[i] if i<len(a) else N([],p))+(b[i] if i<len(b) else N([],p))) for i in range(n)]
        def pgcd(a, b):
            a, b = strip(list(a)), strip(list(b))
            while b:
                _, r = pdivmod(a, b); a, b = b, r
            ia = inv(a[-1]); return [red(x*ia) for x in a]
        def pxgcd(a,b):
            r0,r1=strip(list(a)),strip(list(b)); s0,s1=[N([1],p)],[]; t0,t1_=[],[N([1],p)]
            while r1:
                q,r=pdivmod(r0,r1); r0,r1=r1,r
                s0,s1=s1,padd(s0,[red(-x) for x in pmul(q,s1)]) if s1 else padd(s0,[])
                t0,t1_=t1_,padd(t0,[red(-x) for x in pmul(q,t1_)]) if t1_ else padd(t0,[])
            return r0,s0,t0
        g = pgcd(fK, gK); assert len(g)==2, ('gcd degree', len(g)-1)
        rho = red(-g[0])
        Pq, r1 = pdivmod(fK, [red(-rho), N([1],p)]); assert not r1
        Qq, r2 = pdivmod(gK, [red(-rho), N([1],p)]); assert not r2
        r0,A,Bb = pxgcd(Pq,Qq); assert len(r0)==1
        ir=inv(r0[0]); A=strip([red(x*ir) for x in A]); Bb=strip([red(x*ir) for x in Bb])
        def ints(l): return [[int(x) for x in y.coeffs()] for y in l]
        Pn = pack([[int(x) for x in P.coeffs()]]); rhon = pack([[(-int(x)) % p for x in rho.coeffs()]])
        Pqn = pack(ints(Pq)); Qqn = pack(ints(Qq)); an = pack(ints(A)); bn = pack(ints(Bb))
        F = pack(Fbar); G = pack(Gbar)
        def eqw(lhs, rhs, nx):
            Lh = unpack(lhs, nx); R = unpack(rhs, nx); H=[]
            for k in range(nx):
                e = N([(Lh[k][j]-R[k][j]) % p for j in range(WT)], p)
                q, r = divmod(e, P); assert r == 0
                H.append([int(x) for x in q.coeffs()])
            PH = unpack(Pn*pack(H), nx); Gp=[];Gm=[]
            for k in range(nx):
                rp=[];rm=[]
                for j in range(WT):
                    d = Lh[k][j]-R[k][j]-PH[k][j]; assert d % p == 0; gq = d//p
                    rp.append(max(-gq,0)); rm.append(max(gq,0))
                Gp.append(rp); Gm.append(rm)
            return pack(H), pack(Gp), pack(Gm)
        Hf,Gfp,Gfm = eqw(F, (Pqn << (SB*WT)) + rhon*Pqn, 66)
        Hg,Ggp,Ggm = eqw(G, (Qqn << (SB*WT)) + rhon*Qqn, 65)
        Hab,Gap,Gam = eqw(an*Pqn + bn*Qqn, 1, 129)
        assert F + p*Gfp == (Pqn << (SB*WT)) + rhon*Pqn + Pn*Hf + p*Gfm
        assert G + p*Ggp == (Qqn << (SB*WT)) + rhon*Qqn + Pn*Hg + p*Ggm
        assert an*Pqn + bn*Qqn + p*Gap == 1 + Pn*Hab + p*Gam
        lits.update({f'P{idx}':Pn, f'rho{idx}':rhon, f'Pq{idx}':Pqn, f'Qq{idx}':Qqn, f'a{idx}':an, f'b{idx}':bn,
                     f'Hf{idx}':Hf, f'Hg{idx}':Hg, f'Hab{idx}':Hab, f'Gfp{idx}':Gfp, f'Gfm{idx}':Gfm,
                     f'Ggp{idx}':Ggp, f'Ggm{idx}':Ggm, f'Gap{idx}':Gap, f'Gam{idx}':Gam})
    # product chain with single rows of width 343
    WS = 343
    def pack1(l): return pack([l], WS)
    T = [int(x) for x in fac[0].coeffs()]
    Tn = pack1(T)
    chain = {}
    for i in range(1,7):
        Pi = [int(x) for x in fac[i].coeffs()]
        prod = Tn * pack1(Pi)
        Tnext = [int(x) for x in (N(T,p)*fac[i]).coeffs()]
        Tnextn = pack1(Tnext)
        slots = unpack(prod, 1, WS)[0]; slotsT = unpack(Tnextn, 1, WS)[0]
        Gp=[];Gm=[]
        for j in range(WS):
            d = slots[j]-slotsT[j]; assert d % p == 0; gq=d//p
            Gp.append(max(gq,0)); Gm.append(max(-gq,0))
        # identity: Tn * Pn + p*Gm = Tnext + p*Gp
        assert Tn*pack1(Pi) + p*pack1(Gm) == Tnextn + p*pack1(Gp)
        chain[f'T{i}'] = Tnextn; chain[f'Cm{i}'] = pack1(Gm); chain[f'Cp{i}'] = pack1(Gp)
        T = Tnext; Tn = Tnextn
    # final: lc * T7 ≡ S mod p
    Sred = [v % p for v in St]
    slots = [lcS*x for x in unpack(Tn,1,WS)[0]]
    Gp=[];Gm=[]
    for j in range(WS):
        d = slots[j]-Sred[j]; assert d % p == 0; gq=d//p
        Gp.append(max(gq,0)); Gm.append(max(-gq,0))
    assert lcS*Tn + p*pack1(Gm) == pack1(Sred) + p*pack1(Gp)
    chain['Um'] = pack1(Gm); chain['Up'] = pack1(Gp)
    def rows(n, wt):
        RW = SB*wt; out=[]
        while n:
            out.append(n & ((1<<RW)-1)); n >>= RW
        return out or [0]
    lines=["import Sz8.Galois.Packed", "", "/-! Generated by `galois/nodedata.py`: residue witnesses for the seven factors of `S̄`",
     "modulo `1000003` (sorted by degree 1, 3, 5, 14, 78, 84, 157), the factor-product chain, and `S̃`. -/", "",
     "namespace Sz8.Galois.NodeData", "",
     "/-- Join rows (least significant first), `w` bits per row. -/",
     "def join (w : Nat) : List Nat → Nat", "  | [] => 0", "  | r :: rs => r + (join w rs <<< w)", ""]
    for k,v in lits.items():
        body = ",\n  ".join(f"0x{r:x}" for r in rows(v, WT))
        lines.append(f"def {k}R : List Nat := [\n  {body}]")
        lines.append(f"def {k} : Nat := join (64 * 313) {k}R")
    for k,v in chain.items():
        body = ",\n  ".join(f"0x{r:x}" for r in rows(v, 16))
        lines.append(f"def {k}R : List Nat := [\n  {body}]")
        lines.append(f"def {k} : Nat := join (64 * 16) {k}R")
    lines.append(f"def lcS : Nat := {lcS}")
    lines.append("/-- `S̃`: the node polynomial, primitive with integer coefficients, ascending. -/")
    lines.append("def Slist : List Int := [\n  " + ",\n  ".join(str(v) for v in St) + "]")
    lines.append("\nend Sz8.Galois.NodeData")
    return "\n".join(lines)+"\n"
