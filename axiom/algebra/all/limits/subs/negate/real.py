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


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:Interval(a, b, left_open=True)](f(x) > 0), x, c - x)

    Eq << algebra.equivalent.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.all.imply.all.limits.subs.negate.real, x, c - x)

    Eq << Eq[-1].this.rhs.apply(algebra.all.imply.all.limits.subs.negate.real, x, c - x)

    

    

    


if __name__ == '__main__':
    run()