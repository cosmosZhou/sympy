from axiom.utility import prove, apply
from sympy import *
from sympy.sets.conditionset import conditionset
from axiom import algebre

    
@apply(imply=True)
def apply(n):    
    assert n > 0
    x = Symbol.x(integer=True, nonnegative=True, shape=(oo,))
    P = Symbol("P", definition=conditionset(x[:n], Equality(x[:n].set_comprehension(), Interval(0, n - 1, integer=True))))
    return Unequal(P, P.etype.emptySet) 


@prove
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True, given=True)
    Eq << apply(n)
    
    x = Eq[0].rhs.variable.base
    P = Eq[0].lhs
    Eq << Exists[x[:n]](Contains(x[:n] , P), plausible=True)
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[-1].this.function.rhs.definition
    
    i = Symbol.i(integer=True)
    
    Eq << algebre.exists.given.exists.subs.apply(Eq[-1], x[:n], LAMBDA[i:n](i))
    
    Eq << Eq[-1].this.lhs.simplify()
    
    
if __name__ == '__main__':
    prove(__file__)
