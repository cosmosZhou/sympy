from util import *


@apply(given=None)
def apply(self, old, new):
    from axiom.algebra.all.limits.subs.negate.real import limits_subs
    return Equivalent(self, limits_subs(Any, self, old, new), evaluate=False)


@prove(proved=False)
def prove(Eq):
    from axiom import algebra, sets
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)
    f = Function.f(real=True)
    Eq << apply(Any[x:Interval(a, b, right_open=True)](f(x) > 0), x, c - x)
    
    Eq << Eq[-1].this.rhs.apply(algebra.product.bool)
    
    Eq << Eq[-1].this.rhs.apply(algebra.product.limits.negate.infinity)
    
    Eq << Eq[-1].this.rhs.find(Contains).apply(sets.contains.negate)
    
    Eq << Eq[-1].this.rhs.limits_subs(i, i - c)
    
    Eq << Eq[-1].this.rhs.find(Contains).apply(sets.contains.add, c)
    
    Eq << Eq[-1].this.lhs.apply(algebra.product.bool)


if __name__ == '__main__':
    run()