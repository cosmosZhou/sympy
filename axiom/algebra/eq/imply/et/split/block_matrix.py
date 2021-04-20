from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom


@apply
def apply(given, indices):
    lhs, rhs = axiom.is_Equal(given)
    lhs = lhs.bisect(indices)
    rhs = rhs.bisect(indices)
    assert lhs.is_BlockMatrix and rhs.is_BlockMatrix
    return And(*[Equal(lhs, rhs) for lhs, rhs in zip(lhs.args, rhs.args)])


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n + 1,))
    y = Symbol.y(real=True, shape=(oo,))
    Eq << apply(Equal(x, y[:n + 1]), Slice[-1:])    
    
    Eq << algebra.et.given.cond.apply(Eq[-1])
    
    Eq << Eq[0][:n]
    
    Eq << Eq[0][n]
    

if __name__ == '__main__':
    prove()

