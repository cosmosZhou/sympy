from sympy import *
from axiom.utility import prove, apply
# P is condition set;


@apply
def apply(P):
    definition = P.definition
    assert definition.is_ConditionSet    
    x = definition.variable
    return ForAll[x:P](definition.limits[0][1])


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)
    P = Symbol.P(conditionset(x[:n], Equal(x[:n].set_comprehension(), Interval(0, n - 1, integer=True))))
    Eq << apply(P)
    
    Eq << ForAll[x[:n]:P](Contains(x[:n], P), plausible=True)
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[-1].this.function.subs(Eq[0])
    

if __name__ == '__main__':
    prove()

