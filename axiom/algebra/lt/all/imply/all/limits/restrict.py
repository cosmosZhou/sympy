from util import *


@apply
def apply(le, given):
    c, _b = le.of(Less)
    function, (x, *ab) = given.of(All)
    if len(ab) == 2:
        a, b = ab
        limit = (x, a, c)
    else:
        [ab] = ab
        a, b = ab.of(Interval)
        limit = (x, Interval(a, c, left_open=ab.left_open))
    assert _b == b

    return All(function, limit)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    c = Symbol.c(real=True, given=True)
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    Eq << apply(c < b, All[x:Interval(a, b, right_open=True)](f(x) > 0))

    e = Symbol.e(positive=True)
    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[1], Interval(a, b - e))

    Eq << algebra.cond.imply.suffice.unbounded.apply(Eq[-1], e)

    e = Eq[-1].lhs.lhs
    Eq << Eq[-1].subs(e, b - c)

    Eq << algebra.lt.imply.is_positive.apply(Eq[0])

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
