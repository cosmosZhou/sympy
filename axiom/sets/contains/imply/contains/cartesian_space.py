from axiom.utility import plausible
from sympy.sets.contains import Contains
from sympy import Symbol
from sympy.sets.sets import Interval, CartesianSpace
import axiom
from sympy import LAMBDA
from sympy.core.numbers import oo
from sympy.core.symbol import dtype


@plausible
def apply(given, *limits):
    e, S = axiom.is_Contains(given)    
    
    shape = []
    for limit in limits:
        x, a, b = limit
        assert a == 0 
        assert x.is_integer
        assert e._has(x)
        shape.append(b + 1)
    shape.reverse()
    return Contains(LAMBDA(e, *limits).simplify(), CartesianSpace(S, *shape))


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(integer=True, shape=(oo,))
    S = Symbol.S(etype=dtype.integer)
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    
    Eq << apply(Contains(x[i], S), (i, 0, n - 1))
    
    Eq << Eq[1].simplify()

    
if __name__ == '__main__':
    prove(__file__)

