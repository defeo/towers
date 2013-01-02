from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import Zp
from sage.rings.finite_rings.constructor import GF
from sage.rings.finite_rings.integer_mod_ring import Integers
from sage.rings.arith import CRT, factor
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.misc.functional import cyclotomic_polynomial
from itertools import izip_longest

def _torsion_poly(ell, mod=None):
    """
    Computes the ell-th gauss period modulo `mod`. It uses a
    multi-modular algorithm.

    This is my favourite equality:
    
    sage: all(_torsion_poly(n)(I) == I^n*lucas_number2(n,1,-1) for n in range(1,10))
    True
    """
    def tp_prime(Rs, ell):
        "Multimodular algorithm to compute the non-null coefficients"
        t = [[R(1) for R in Rs]]
        for k in range(1, ell/2 + 1):
            m = ZZ(ell - 2*k + 2) * (ell - 2*k + 1) / ((ell - k) * k)
            t.append([-c * m for c in t[-1]])
        return t

    if mod is None:
        t = sum(map(lambda x:(x[0], 0), tp_prime([ZZ], ell)), ())
        R = ZZ
    else:
        fact = factor(mod)
        moduli = [p**e for (p,e) in fact]
        ts = tp_prime([Zp(p, prec=e, type='capped-rel')
                       for (p,e) in fact],
                      ell)
        ts = map(lambda x:map(lambda (c,(_,e)):c.residue(e).lift(), 
                              zip(x,fact)),
                 ts)
        t = sum(map(lambda x:(CRT(x, moduli), 0), ts), ())
        R = Integers(mod)

    P = PolynomialRing(R, 'x')
    return P(list(reversed(t))).shift(ell % 2 - 1)


class Tower:
    def __init__(self, K, ell, name, debug=False):
        """
        Initialize the ell-adic extension tower of K.
        """
        if not K.is_finite() and not K.is_prime_field():
            raise RuntimeError('Only works for prime fields.')
        if (K.characteristic() + 1) % ell != 0:
            raise RuntimeError('The degree must divide ' +
                               str(K.characteristic() + 1) + '.')
        if ell % 2 == 0:
            raise RuntimeError('The degree must be odd.')

        self._base = K
        self._degree = ell
        self._name = name
        self._t = _torsion_poly(ell, K.characteristic())
        self._levels = [K]
        self._minpolys = [None]
        self._eta = cyclotomic_polynomial(ell).factor_mod(K.characteristic())[0][0][1]
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
                              self._base.characteristic()) - self._eta
        self._minpolys.append(p)

        k = self._levels[-1]
        K = GF(k.cardinality()**self._degree, 
               name=self._name + str(len(self._levels)),
               modulus=p,
               check_irreducible=self._debug)
        self._levels.append(K)

    def _push_down(self, x):
        f = self._t
        P = f.parent(x.polynomial())
        level = x.parent().degree().valuation(self._degree)

        def decompose(P, f):
            if P.degree() < f.degree() * 2:
                return P.quo_rem(f)
            else:
                return sum((g.quo_rem(f) for g in decompose(P, f**2)), ())

        return [self[level-1](list(reversed(c)))
                for c in izip_longest(*decompose(P, f))]

    def _lift_up(self, xs):
        f = self._t
        Ps = list(izip_longest(*map(lambda x:x.polynomial(), xs)))
        level = xs[0].parent().degree().valuation(self._degree)

        def compose(Ps, f):
            if len(Ps) == 0:
                return f.parent()(0)
            elif len(Ps) == 1:
                return f.parent()(Ps[0])
            else:
                g = f**2
                return compose(Ps[::2], g) + f*compose(Ps[1::2], g)

        return self[level+1](compose(Ps, f))
