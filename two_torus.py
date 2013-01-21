from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import Zp
from sage.rings.finite_rings.constructor import GF
from sage.rings.finite_rings.integer_mod_ring import Integers
from sage.rings.arith import CRT, factor, valuation
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.misc.functional import cyclotomic_polynomial
from itertools import izip_longest
from de_compose import *

def _torsion_poly(ell, P=None):
    """
    Computes the ell-th gauss period. If `P` is given, it must be a
    polynomial ring into which te result is coerced.

    This is my favourite equality:
    
    sage: all(_torsion_poly(n)(I) == I^n*lucas_number2(n,1,-1) for n in range(1,10))
    True
    """
    if P is None:
        P, R, = PolynomialRing(ZZ, 'x'), ZZ, 
    elif P.characteristic() == 0:
        R = ZZ
    else:
        R = Zp(P.characteristic(), prec=1, type='capped-rel')
    
    t = [1, 0]
    for k in range(1, ell/2 + 1):
        m = R(ell - 2*k + 2) * R(ell - 2*k + 1) / (R(ell - k) * R(k))
        t.append(-t[-2] * m)
        t.append(0)

    return P(list(reversed(t))).shift(ell % 2 - 1)


# Montgomery ladder for Pell conics
def _pellmul(x, n):
    # The zero point and ours
    A, B = 2, x
    for c in reversed(n.digits(2)):
        if c == 0:
            A, B = A**2 - 2, A*B - x
        else:
            A, B = A*B - x, B**2 - 2
    return A


class Tower:
    def __init__(self, K, ell, name, implementation=None, debug=False):
        """
        Initialize the ell-adic extension tower of K.
        """
        p = K.characteristic()

        if not K.is_finite():
            raise RuntimeError('The field must be finite.')
        if  not K.is_prime_field():
            raise NotImplementedError('Only works for prime fields.')
        if (p + 1) % ell != 0:
            raise RuntimeError('The degree must divide %d.' % (p + 1))
        if ell % 2 == 0:
            raise RuntimeError('The degree must be odd.')

        # Find an element of maximal order on the Pell conic
        eta = K(1)
        if p != 2:
            o = (p + 1) // ell
            while (eta**2 - 4).is_square() or _pellmul(eta, o) == 2:
                eta = K.random_element()

        self._base = K
        self._P = PolynomialRing(K, name, implementation=implementation)
        self._degree = ell
        self._name = name
        self._t = _torsion_poly(ell, self._P)
        self._levels = [K]
        self._minpolys = [None]
        self._eta = eta
        self._debug = debug

    def __getitem__(self, i):
        for j in range(len(self._levels), i+1):
            self._add_one_level()
        return self._levels[i]

    def _add_one_level(self):
        if len(self._levels) == 1:
            p = self._t - self._eta
        else:
            p = _torsion_poly(self._degree**len(self._levels),
                              self._P) - self._eta
        self._minpolys.append(p)

        if self._debug and not p.is_irreducible():
            raise RuntimeError('Polynomial must be irreducible')

        K = self._P.quo(p, self._name + str(len(self._levels)))
        self._levels.append(K)

    def _push(self, x):
        f = self._t
        level = valuation(x.parent().degree(), self._degree)

        p = [self[level-1](list(c))
             for c in izip_longest(*decompose(x.lift(), f), fillvalue=0)]
        return p if p else [self[level-1](0)]

    def _lift(self, xs):
        if not xs:
            raise RuntimeError("Don't know where to lift to.")

        f = self._t
        Ps = map(self._P.__call__, izip_longest(*xs))
        level = valuation(xs[0].parent().degree(), self._degree)

        return self[level+1](compose(Ps, f))
