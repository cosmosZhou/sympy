from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply
def apply(given):
    fn, *limits = axiom.forall_ne(given)
    lhs, rhs = axiom.limit_is_set(limits)
    x, y = fn.args
    if x == lhs: 
        return NotContains(y, rhs)
    if y == lhs:
        return NotContains(x, rhs)


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True, given=True)
    n = Symbol.n(integer=True, positive=True, given=True)
 
    Eq << apply(ForAll[i:n](Unequality(i, j)))
    
    Eq << ~Eq[-1]
    
    Eq << sets.contains.imply.exists_eq.definition.apply(Eq[-1], reverse=True)
    
    Eq << ~Eq[-1]

    
if __name__ == '__main__':
    prove(__file__)

