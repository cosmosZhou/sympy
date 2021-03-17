from axiom.utility import prove, apply
from sympy.core.relational import Equality, LessThan
from sympy import Symbol
import axiom


@apply
def apply(*given):
    less_than, equal = given
    k, n = axiom.is_LessThan(less_than)
    a, b = axiom.is_Equal(equal)
    assert a.shape == b.shape
    assert n <= a.shape[0] == b.shape[0]
    
    return Equality(a[:k], b[:k])

@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n,))
    y = Symbol.y(real=True, shape=(n,))
    Eq << apply(LessThan(k, n), Equality(x, y))
    
    Eq << Eq[-1].subs(Eq[1])
    

if __name__ == '__main__':
    prove(__file__)

