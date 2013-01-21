"""
  The two test routines take three parameters:
    p : size of the base field
    l : degree of the tower
    h : height of the tower

  and return a list of lists containing timings (in seconds) for
  various operations (create, embed, push, lift) at each level.

  Two optional parameters 'number' and 'repeat' allow influencing the
  timeit machine (for lift and push only). See 

    sage: ?sage_timeit

  They also print some summary of timings for convenience.
"""


import two_torus as T2
import elliptic as EC
from sage.rings.finite_rings.constructor import GF
from sage.misc.sage_timeit import sage_timeit

def test(p, l, h, T, implementation=None, number=0, repeat=3):
    """
    This subroutine does the real job
    """
    tower = T(GF(p), l, 'x', implementation=implementation)
    
    tcreat, tlift, tpush = [], [], []
    for i in range(1, h+1):
        context = globals()
        context.update(locals())
        tcreat.append(sage_timeit('tower[i]', context, number=1, repeat=1, seconds=True))

        if i > 1:
            tpush.append(sage_timeit('tower._push(tower[i].random_element())', 
                                     context, number=number, repeat=repeat, seconds=True))
            tlift.append(sage_timeit('tower._lift([tower[i-1].random_element() for k in range(l)])',
                                     context, number=number, repeat=repeat, seconds=True))

    print 'Creation time:', sum(tcreat)
    print 'Push time:', sum(tpush)
    print 'Lift time:', sum(tlift)

    return tcreat, tpush, tlift
    

def test_torus(p, l, h, implementation=None, number=0, repeat=3):
    "Tests the T2 construction"
    return test(p, l, h, T2.Tower, implementation, number, repeat)

def test_elliptic(p, l, h, implementation=None, number=0, repeat=3):
    "Tests C&L construction"
    return test(p, l, h, EC.Tower, implementation, number, repeat)

