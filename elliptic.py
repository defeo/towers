from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import Zp
from sage.rings.finite_rings.constructor import GF
from sage.rings.finite_rings.integer_mod_ring import Integers
from sage.rings.arith import CRT, factor, valuation
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.schemes.elliptic_curves.constructor import EllipticCurve_from_j
from itertools import izip_longest
from de_compose import *

class Tower:
    def __init__(self, K, ell, name, implementation=None, debug=False):
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

        self._P = PolynomialRing(K, name, implementation=implementation)
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

            f = self._P(i[0].numerator())
            g = self._P(i[0].denominator())
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
                else (self._P.gen(), self._P(1)))
        F = compose(list(F), f, g)
        G = g*compose(list(G), f, g)
        self._abs_polys.append((F, G))
        p = F - self._eta*G

        if self._debug and not p.is_irreducible():
            raise RuntimeError('Polynomial must be irreducible')

        K = self._P.quo(p, self._name + str(len(self._levels)))
        self._levels.append(K)

    def _push(self, x):
        level = valuation(x.parent().degree(), self._degree)
        f, g = self._rel_polys[-level % len(self._rel_polys)]
        deg = self._degree**(level - 1) - 1
        x *= x.parent(g**deg)

        p = [self[level-1](list(c))
             for c in izip_longest(*decompose(x.lift(), f, g, deg), fillvalue=0)]
        return p if p else [self[level-1](0)]

    def _lift(self, xs):
        if not xs:
            raise RuntimeError("Don't know where to lift to.")

        level = valuation(xs[0].parent().degree(), self._degree)
        f, g = self._rel_polys[(-level-1) % len(self._rel_polys)]
        Ps = map(self._P.__call__, izip_longest(*xs))

        return (self[level+1](compose(Ps, f, g)) / 
                self[level+1](g**(len(Ps)-1)))
