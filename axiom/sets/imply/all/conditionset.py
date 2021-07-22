from util import *
# P is condition set;


@apply
def apply(P):
    definition = P.definition
    assert definition.is_ConditionSet    
    x = definition.variable
    return All[x:P](definition.limits[0][1])


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)
    P = Symbol.P(conditionset(x[:n], Equal(x[:n].set_comprehension(), Range(0, n))))
    Eq << apply(P)
    
    Eq << All[x[:n]:P](Contains(x[:n], P), plausible=True)
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[-1].this.expr.subs(Eq[0])
    

if __name__ == '__main__':
    run()

