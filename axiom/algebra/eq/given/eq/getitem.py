from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(imply, i=None):
    x, y = axiom.is_Equal(imply)
    assert x.shape == y.shape 
    
    if isinstance(i, (tuple, Tuple)):
        shape = x.shape 
        for i_, n in zip(i, shape):
            assert i_.domain == Interval(0, n - 1, integer=True)
    else:
        n = x.shape[0]    
        assert i.domain == Interval(0, n - 1, integer=True)
    
    return Equal(x[i], y[i])


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    a = Symbol.a(shape=(n,), etype=dtype.integer)
    b = Symbol.b(shape=(n,), etype=dtype.integer)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    
    Eq << apply(Equal(a, b), i=i)

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[1], (i,))


if __name__ == '__main__':
    prove()

