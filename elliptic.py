from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import Zp
from sage.rings.finite_rings.constructor import GF
from sage.rings.finite_rings.integer_mod_ring import Integers
from sage.rings.arith import CRT, factor
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.schemes.elliptic_curves.constructor import EllipticCurve_from_j
from itertools import izip_longest
from de_compose import *

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
        F = compose(list(F), f, g)
        G = g*compose(list(G), f, g)
        self._abs_polys.append((F, G))
        p = F - self._eta*G

        k = self._levels[-1]
        K = GF(k.cardinality()**self._degree, 
               name=self._name + str(len(self._levels)),
               modulus=p,
               check_irreducible=self._debug)
        self._levels.append(K)

    def _push(self, x):
        level = x.parent().degree().valuation(self._degree)
        f, g = self._rel_polys[-level % len(self._rel_polys)]
        deg = self._degree**(level - 1) - 1
        x *= x.parent(g**deg)
        P = f.parent(x.polynomial())

        return [self[level-1](list(c))
                for c in izip_longest(*decompose(P, f, g, deg))]

    def _lift(self, xs):
        level = xs[0].parent().degree().valuation(self._degree)
        f, g = self._rel_polys[(-level-1) % len(self._rel_polys)]
        Ps = map(f.parent().__call__, izip_longest(*map(lambda x:x.polynomial(), xs)))

        return (self[level+1](compose(Ps, f, g)) / 
                self[level+1](g**(len(Ps)-1)))
