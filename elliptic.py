from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import Zp
from sage.rings.finite_rings.constructor import GF
from sage.rings.finite_rings.integer_mod_ring import Integers
from sage.rings.arith import CRT, factor
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.schemes.elliptic_curves.constructor import EllipticCurve_from_j
from itertools import izip_longest

def _compose(Ps, f, g):
    if len(Ps) == 0:
        return f.parent()(0)
    elif len(Ps) == 1:
        return f.parent()(Ps[0])
    else:
        f2, g2 = f**2, g**2
        P0 = _compose(Ps[::2], f2, g2)
        P1 = _compose(Ps[1::2], f2, g2)
        if len(Ps) % 2 == 0:
            return g*P0 + f*P1
        else:
            return P0 + g*f*P1


def _decompose(P, f, g, target):
    "Assumes deg f >= deg g"

    def dec(P, f, g, invf, invg):
        a = f.parent()(0)
        if P.degree() >= f.degree() + g.degree():
            a, P = P.quo_rem(f)
            
        return a + (P * invf) % g, (P * invg) % f
        
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


class Tower:
    def __init__(self, K, ell, name, debug=False):
        """
        Initialize the ell-adic extension tower of K.
        """
        if not K.is_finite() or not K.is_prime_field():
            raise RuntimeError('Only works for prime fields.')
        if not ell.is_prime():
            raise RuntimeError('The degree must be prime.')
        if (K.cardinality() - 1) % ell == 0:
            raise RuntimeError('The degree must not divide ' + str(K.cardinality()-1) + '.')
        if K.characteristic() == ell:
            raise RuntimeError('The degree must not equal the characteristic.')
        if K.cardinality() + 2*K.cardinality() <= ell:
            raise RuntimeError('The degree must be smaller than the Hasse bound.')

        # find a curve with the right number of points
        t = 1
        p = K.cardinality()
        while (p+1-t) % ell !=0 and (p+1+t) % ell !=0:
            E = EllipticCurve_from_j(K.random_element())
            t = E.trace_of_frobenius()

        if (p+1-t) % ell !=0:
            E = E.quadratic_twist()
            c = p+1+t
        else:
            c = p+1-t

        # Find a point of maximal ell-order on the last curve
        P = E(0)
        while (P * ell**(c.valuation(ell)-1)).is_zero():
            P = E.random_point() * c.prime_to_m_part(ell)
        self._eta = P[0]

        # Run through the isogeny cycle
        self._rel_polys = []
        baseE = E
        iso = None
        while iso is None:
            # Construct the next ell-isogeny
            P = E(0)
            while P.is_zero():
                P = E.random_point() * c.prime_to_m_part(ell)
            while not (P*ell).is_zero():
                P *= ell
            i = E.isogeny(P)

            f = i[0].numerator().univariate_polynomial()
            g = i[0].denominator().univariate_polynomial()
            E = i.codomain()
            if E.is_isomorphic(baseE):
                iso = E.isomorphism_to(baseE)
                g *= iso.u**2
            self._rel_polys.append((f, g))

        self._base = K
        self._degree = ell
        self._name = name
        self._levels = [K]
        self._abs_polys = []
        self._debug = debug

    def __getitem__(self, i):
        for j in range(len(self._levels), i+1):
            self._add_one_level()
        return self._levels[i]

    def _add_one_level(self):
        f, g = self._rel_polys[-len(self._levels) % 
                                len(self._rel_polys)]
        
        F, G = (self._abs_polys[-1] 
                if self._abs_polys
                else (f.parent().gen(), f.parent()(1)))
        F = _compose(list(F), f, g)
        G = g*_compose(list(G), f, g)
        self._abs_polys.append((F, G))
        p = F - self._eta*G

        k = self._levels[-1]
        K = GF(k.cardinality()**self._degree, 
               name=self._name + str(len(self._levels)),
               modulus=p,
               check_irreducible=self._debug)
        self._levels.append(K)

    def _push_down(self, x):
        level = x.parent().degree().valuation(self._degree)
        f, g = self._rel_polys[-level % len(self._rel_polys)]
        deg = self._degree**(level - 1) - 1
        x *= x.parent(g**deg)
        P = f.parent(x.polynomial())

        return [self[level-1](list(c))
                for c in izip_longest(*_decompose(P, f, g, deg))]

    def _lift_up(self, xs):
        level = xs[0].parent().degree().valuation(self._degree)
        f, g = self._rel_polys[(-level-1) % len(self._rel_polys)]
        Ps = list(izip_longest(*map(lambda x:x.polynomial(), xs)))

        return (self[level+1](_compose(Ps, f, g)) / 
                self[level+1](g**(len(Ps)-1)))
