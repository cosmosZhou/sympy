from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply
def apply(given):
    fn, *limits = axiom.forall_unequal(given)
    contains = axiom.limit_is_set(limits)
    x, y = fn.args
    if x == contains.lhs: 
        return NotContains(y, contains.rhs)
    if y == contains.lhs:
        return NotContains(x, contains.rhs)


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True, given=True)
    n = Symbol.n(integer=True, positive=True, given=True)
 
    Eq << apply(ForAll[i:n](Unequality(i, j)))
    
    Eq << ~Eq[-1]
    
    Eq << sets.contains.imply.exists_equal.definition.apply(Eq[-1], reverse=True)
    
    Eq << ~Eq[-1]

    
if __name__ == '__main__':
    prove(__file__)

