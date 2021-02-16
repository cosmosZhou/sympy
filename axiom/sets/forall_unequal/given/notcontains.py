from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply(given=True)
def apply(imply):
    fn, *limits = axiom.forall_unequal(imply)
    contains = axiom.limit_is_set(limits)
    x, y = fn.args
    if x == contains.lhs: 
        return NotContains(y, contains.rhs)
    if y == contains.lhs:
        return NotContains(x, contains.rhs)


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
 
    Eq << apply(ForAll[i:n](Unequality(i, j)))
    
    Eq << sets.notcontains.imply.forall_unequal.apply(Eq[1], reverse=True)

    
if __name__ == '__main__':
    prove(__file__)

