def compose(Ps, f, g=1):
    "Compute the numerator of Ps(f/g). Ps is a list of coefficients."
    n = len(Ps)
    
    def color(i, n, h):
        while h > 0:
            if bool(i & 1) == bool(n & (1 << (h - 1))):
                return bool(i & 1)
            i = i // 2
            h -= 1
        return False

    res = []
    ptr = 0
    h = n.bit_length() - 1
    for i in range(1 << h):
        if color(i, n, h):
            res.append(g*Ps[ptr] + f*Ps[ptr+1])
            ptr += 2
        else:
            res.append(Ps[ptr])
            ptr += 1
    Ps = res

    ll, lh = 1, g
    rl, rh = 1, f
    for h in reversed(range(n.bit_length() - 1)):
        if n & (1 << (h + 1)):
            ll, lh = ll * lh, lh**2
            rl, rh = rl * rh, rh**2
        else:
            ll, lh = ll**2, ll * lh
            rl, rh = rl**2, rl * rh
        res = []
        b = n & (1 << h)
        for i in range(1 << h):
            col = color(i, n, h)
            if col and b:
                res.append(lh*Ps[2*i] + rh*Ps[2*i+1])
            elif col or b:
                res.append(lh*Ps[2*i] + rl*Ps[2*i+1])
            else:
                res.append(ll*Ps[2*i] + rl*Ps[2*i+1])
        Ps = res

    return Ps[0]


def decompose(P, f, g=None, target=None):
    """
    Compute a polynomial Q of degree target such that compose(Q, f,
    g).  Assumes deg f >= deg g. The result is returned as a list of
    coefficients.
    """

    def dec(P, f, g, invf, invg):
        a = f.parent()(0)
        if P.degree() >= f.degree() + g.degree():
            a, P = P.quo_rem(f)
            
        return a + (P * invf) % g, (P * invg) % f
        
    if g is None:
        g = f.parent()(1)
    if target is None:
        target = P.degree() // f.degree()
    n, a, b = 0, 1, 1
    moduli = []
    for bit in reversed(target.bits()):
        if bit:
            n1, a1, b1 = n+1, a*f, b*g
        else:
            n1, a1, b1 = n, a, b
        moduli.append((n1, a1, b1))
        n, a, b = n + n1, a*a1, b*b1

    res = {0: P}
    for n, a, b in reversed(moduli):
        newres = {}
        _, inva, invb = a.xgcd(b)
        for i, p in res.iteritems():
            p0, p1 = dec(p, a, b, inva, invb)
            newres[i+n] = p0 + newres.get(i+n, 0)
            newres[i] = p1 + newres.get(i, 0)
        res = newres

    return [res[i] for i in range(len(res))]
