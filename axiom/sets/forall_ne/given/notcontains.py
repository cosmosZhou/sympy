from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply
def apply(imply):
    fn, *limits = axiom.forall_ne(imply)
    lhs, rhs = axiom.limit_is_set(limits)
    x, y = fn.args
    if x == lhs: 
        return NotContains(y, rhs)
    if y == lhs:
        return NotContains(x, rhs)


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
 
    Eq << apply(ForAll[i:n](Unequality(i, j)))
    
    Eq << sets.notcontains.imply.forall_ne.apply(Eq[1], reverse=True)

    
if __name__ == '__main__':
    prove(__file__)

