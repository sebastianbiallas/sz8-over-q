#!/usr/bin/env python3
"""Suzuki group data: the text of Sz8/Galois/SuzukiData.lean, and consistency checks for Sz8/Galois/Suzuki.lean.

* `F8 = F2[z]/(z^3 + z + 1)`, elements as 3-bit integers (`z = 2`), `θ(x) = x^4`.
* The ovoid: the orbit of (0,0,0,1) under the column action of T(a,b), M(κ), W, in breadth-first order.
* The labelling: GAP's `RepresentativeAction(S65, P, N)` (`inputs/suzuki_conj.txt`, produced by
  `upstream/suzuki/run_gap.py`) moves the ovoid action onto `N`. It is not trusted: Lean checks
  every generator image and the resulting isomorphism.
* Generator images are recomputed from the matrices, sifted through N's transversals (decoded from
  Sz8/Monodromy/GroupCerts.lean), and `Nc1`, `Nc2` are written as words by breadth-first search.

Independent of GAP except for the recorded relabelling."""
import re
from collections import deque

from paths import INPUTS, PROJECT


def mul(a, b):
    r = 0
    for i in range(3):
        if (b >> i) & 1:
            r ^= a << i
    for d in (4, 3):
        if (r >> d) & 1:
            r ^= 0b1011 << (d - 3)
    return r


def inv(a):
    return next(b for b in range(1, 8) if mul(a, b) == 1) if a else 0


def pw(a, n):
    r = 1
    for _ in range(n):
        r = mul(r, a)
    return r


def th(a):
    return pw(a, 4)


assert all(th(th(a)) == mul(a, a) for a in range(8))


def Tm(a, b):
    return [[1, 0, 0, 0], [a, 1, 0, 0], [b, th(a), 1, 0],
            [mul(mul(a, a), th(a)) ^ mul(a, b) ^ th(b), mul(a, th(a)) ^ b, a, 1]]


def Mm(k):
    d = [mul(k, th(k)), k, inv(k), inv(mul(k, th(k)))]
    return [[d[i] if i == j else 0 for j in range(4)] for i in range(4)]


Wm = [[0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0], [1, 0, 0, 0]]
GENS = [Tm(a, b) for a in range(8) for b in range(8)] + [Mm(k) for k in range(1, 8)] + [Wm]


def mv(A, v):
    out = []
    for i in range(4):
        s = 0
        for j in range(4):
            s ^= mul(A[i][j], v[j])
        out.append(s)
    return out


def normalize(v):
    for c in v:
        if c:
            return [mul(inv(c), x) for x in v]
    return v


def labelled():
    """The ovoid in label order and the 72 generator images (T(a,b) at 8a+b, M(κ) at 63+κ, W at 71)."""
    orb = [(0, 0, 0, 1)]
    seen = set(orb)
    for p in orb:
        for g in GENS:
            q = tuple(normalize(mv(g, p)))
            if q not in seen:
                seen.add(q)
                orb.append(q)
    assert len(orb) == 65
    x = [int(v) - 1 for v in re.findall(r'\d+', (INPUTS / 'suzuki_conj.txt').read_text())]
    assert sorted(x) == list(range(65))
    ovoid = [None] * 65
    for i, p in enumerate(orb):
        ovoid[x[i]] = list(p)
    idx = {tuple(p): i for i, p in enumerate(ovoid)}
    perms = [[idx[tuple(normalize(mv(g, p)))] for p in ovoid] for g in GENS]
    return ovoid, perms


def unpack(p):
    return [((p >> (7 * i)) % 128) % 65 for i in range(65)]


def comp(p, q):
    return [p[q[i]] for i in range(65)]  # Lean: (p * q) i = p (q i)


def iso_data():
    ovoid, perms = labelled()
    src = (PROJECT / 'Sz8/Monodromy/GroupCerts.lean').read_text()
    packed = {m.group(1): int(m.group(2)) for m in
              re.finditer(r'^def (\w+) : Equiv\.Perm \(Fin 65\) := ofPacked (\d+) (\d+)', src, re.M)}

    def tvlist(name):
        m = re.search(rf'^def {name} : List \(Equiv\.Perm \(Fin 65\) × List ℕ\) := \[(.*)\]$', src, re.M)
        return [unpack(packed[n]) for n in re.findall(r'\((\w+), \[', m.group(1))]
    T0, T1, T2 = tvlist('Ntvw0'), tvlist('Ntvw1'), tvlist('Ntvw2')
    assert (len(T0), len(T1), len(T2)) == (65, 64, 7)
    Nc1, Nc2 = unpack(packed['Nc1']), unpack(packed['Nc2'])
    table = {}
    for a in range(65):
        for b in range(64):
            ab = comp(T0[a], T1[b])
            for c in range(7):
                table[tuple(comp(ab, T2[c]))] = (a, b, c)
    assert len(table) == 29120
    sift = [table[tuple(p)] for p in perms]
    letters = [9, 1, 65, 71]  # T(1,1), T(0,1), M(z), W
    ident = tuple(range(65))
    prev = {ident: None}
    dq = deque([ident])
    while dq:
        x = dq.popleft()
        for k in letters:
            y = tuple(comp(list(x), perms[k]))
            if y not in prev:
                prev[y] = (x, k)
                dq.append(y)
    assert len(prev) == 29120

    def word(target):
        w, x = [], tuple(target)
        while prev[x] is not None:
            x, k = prev[x]
            w.append(k)
        return w[::-1]
    w1, w2 = word(Nc1), word(Nc2)
    for w, t in ((w1, Nc1), (w2, Nc2)):
        x = list(range(65))
        for k in w:
            x = comp(x, perms[k])
        assert x == t
    return {'ovoid': ovoid, 'perms': perms, 'sift': sift, 'w1': w1, 'w2': w2}


def pack(p):
    return sum(v << (7 * i) for i, v in enumerate(p))


def generate(d=None):
    d = d or iso_data()
    P, sift, w1, w2 = [pack(p) for p in d['perms']], d['sift'], d['w1'], d['w2']
    out = []
    o = out.append
    o('import Sz8.Galois.SuzukiAction')
    o('import Sz8.Galois.NSum')
    o('')
    o('/-!')
    o('# Generator data for `Sz(8)` on the ovoid (generated by `galois/suzuki.py`)')
    o('')
    o('* `gensP[k]`: the recorded image of generator `k` on the 65 labels, packed as in `Sz8.Monodromy.PackedPerm`;')
    o('  `k = 8a + b` is `T(a, b)`, `k = 63 + κ` is `M(κ)`, `k = 71` is `W`.')
    o('* `checkT*`, `checkM`, `checkW`: kernel checks `normalize (G · ov i) = ov (gp k i)` for every generator.')
    o('* `siftOK`: every recorded image is the chain product `NSum.tprod a b c` of the transversals of `N`.')
    o('* `word1OK`, `word2OK`: `Nc1`, `Nc2` are words in the images of `T(1,1)`, `T(0,1)`, `M(z)`, `W`.')
    o('-/')
    o('')
    o('namespace Sz8.Galois.Suzuki')
    o('')
    o('open Sz8.Monodromy')
    o('')
    o('def gensP : List ℕ := [' + ', '.join(map(str, P)) + ']')
    o('')
    o('/-- The recorded image of generator `k`. -/')
    o('def gp (k : ℕ) (i : Fin 65) : Fin 65 := appF (gensP.getD k 0) i')
    o('')
    o('/-- The image check for one generator matrix. -/')
    o('def imgAt (k : ℕ) (G : Matrix (Fin 4) (Fin 4) F8) : Bool :=')
    o('  (List.finRange 65).all fun i => veq (normalize (mv G (ov i))) (ov (gp k i))')
    o('')
    o('def checkTa (a : F8) : Bool := allF8.all fun b => imgAt (8 * a.v.val + b.v.val) (Tmat θ8 a b)')
    o('')
    for a in range(8):
        o(f'theorem checkT{a} : checkTa ⟨{a}⟩ = true := by decide +kernel')
    o('')
    o('theorem checkM : (allF8.all fun κ => κ == 0 || imgAt (63 + κ.v.val) (Mmat θ8 κ)) = true := by decide +kernel')
    o('')
    o('theorem checkW : imgAt 71 Wmat = true := by decide +kernel')
    o('')
    o('def siftL : List (Fin 65 × Fin 64 × Fin 7) := [' + ', '.join(f'({a}, {b}, {c})' for a, b, c in sift) + ']')
    o('')
    o('theorem siftOK : (List.range 72).all (fun k => (List.finRange 65).all fun i =>')
    o('    gp k i == NSum.tprod (siftL.getD k 0).1 (siftL.getD k 0).2.1 (siftL.getD k 0).2.2 i) = true := by')
    o('  decide +kernel')
    o('')
    o('/-- A word `[k₁, …, kₙ]` acts as `gp k₁ ∘ ⋯ ∘ gp kₙ`. -/')
    o('def wfun (w : List ℕ) (i : Fin 65) : Fin 65 := w.foldr (fun k x => gp k x) i')
    o('')
    o('def word1 : List ℕ := [' + ', '.join(map(str, w1)) + ']')
    o('def word2 : List ℕ := [' + ', '.join(map(str, w2)) + ']')
    o('')
    o('theorem word1OK : ((List.finRange 65).all fun i => Nc1 i == wfun word1 i) = true := by decide +kernel')
    o('theorem word2OK : ((List.finRange 65).all fun i => Nc2 i == wfun word2 i) = true := by decide +kernel')
    o('')
    o('end Sz8.Galois.Suzuki')
    return '\n'.join(out) + '\n'


def check_suzuki_lean(text, d=None):
    """The hand-written tables and ovoid list of Suzuki.lean agree with this computation."""
    d = d or iso_data()
    mulP = sum(mul(a, b) << (3 * (8 * a + b)) for a in range(8) for b in range(8))
    invP = sum(inv(a) << (3 * a) for a in range(8))
    assert f'def mulP : ℕ := {mulP}\n' in text, 'mulP differs'
    assert f'def invP : ℕ := {invP}\n' in text, 'invP differs'
    block = text[text.index('def ovoid : List (Fin 4 → F8) :='):]
    block = block[:block.index(']]') + 2]
    rows = [[int(v) for v in re.findall(r'⟨(\d)⟩', r)] for r in re.findall(r'!\[([^\]]*)\]', block)]
    assert rows == d['ovoid'], 'ovoid list differs'
