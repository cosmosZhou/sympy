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
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])
    
    Eq << Eq[-2] @ BlockMatrix([Identity(n), ZeroMatrix(n)]).T
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << BlockMatrix(ZeroMatrix(n), x[n]).this.subs(Eq[3])
    
    Eq << Eq[-1] + Eq[-2]
    
    Eq << Eq[-1].this.lhs.simplify()
    
    Eq << Eq[-1].this.rhs.simplify()
    
if __name__ == '__main__':
    prove()

