from util import *


@apply
def apply(le, given):
    c, _a = le.of(GreaterEqual)
    function, (x, *ab) = given.of(All)
    if len(ab) == 2:
        a, b = ab
        limit = (x, c, b)
    else:
        [ab] = ab
        a, b = ab.of(Interval)
        limit = (x, Interval(c, b, left_open=ab.left_open, right_open=ab.right_open))

    assert _a == a

    return All(function, limit)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(shape=(), real=True)
    Eq << apply(c >= a, All[x:a:b](f(x) > 0))

    e = Symbol(nonnegative=True)
    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[1], Interval(a + e, b))

    Eq << algebra.cond.imply.infer.unbounded.apply(Eq[-1], e)

    e = Eq[-1].lhs.lhs
    Eq << Eq[-1].subs(e, c - a)

    Eq << algebra.ge.imply.ge_zero.apply(Eq[0])

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2019-05-15
# updated on 2019-05-15
