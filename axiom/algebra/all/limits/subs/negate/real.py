from util import *


def limits_subs(All, self, old, new):
    expr, (i, *ab) = self.of(All)
    assert not i.is_integer
    assert old == i
    
    c = new + i
    if len(ab) == 2:
        a, b = ab
        limit = (i, c - b, c - a)
    else:
        [ab] = ab
        a, b = ab.of(Interval)
        limit = (i, Interval(c - b, c - a, left_open=ab.right_open, right_open=ab.left_open))
    
    assert not c._has(i)
    return All(expr._subs(old, new), limit)

@apply(given=None)
def apply(self, old, new):    
    return Equivalent(self, limits_subs(All, self, old, new), evaluate=False)


@prove(proved=False)
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)
    f = Function.f(real=True)
    Eq << apply(All[x:Interval(a, b, left_open=True)](f(x) > 0), x, c - x)

    Eq << Eq[-1].this.rhs.apply(algebra.product.bool)

    Eq << Eq[-1].this.rhs.apply(algebra.product.limits.negate.infinity)

    Eq << Eq[-1].this.rhs.find(Contains).apply(sets.contains.negate)

    Eq << Eq[-1].this.rhs.limits_subs(i, i - c)

    Eq << Eq[-1].this.rhs.find(Contains).apply(sets.contains.add, c)

    Eq << Eq[-1].this.lhs.apply(algebra.product.bool)


if __name__ == '__main__':
    run()