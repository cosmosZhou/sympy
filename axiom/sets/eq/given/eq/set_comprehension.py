from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply
def apply(imply):
    lhs, rhs = axiom.is_Equal(imply)
    
    a = axiom.is_set_comprehension(lhs)
    b = axiom.is_set_comprehension(rhs)
    k = lhs.variable
    return Equal(a[k], b[k])


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(integer=True, shape=(n,))
    b = Symbol.b(integer=True, shape=(n,))
    
    Eq << apply(Equal(a.set_comprehension(), b.set_comprehension()))
    
    i = Eq[0].lhs.variable
    
    Eq << sets.eq.imply.eq.set_comprehension.apply(Eq[-1], (i, 0, n), simplify=None)


if __name__ == '__main__':
    prove()

