from util import *


@apply
def apply(le, given):
    c, a = le.of(Greater)
    function, (x, *ab) = given.of(All)
    if len(ab) == 2:
        S[a], b = ab
        limit = (x, c, b)
    else:
        [ab] = ab
        S[a], b = ab.of(Interval)
        limit = (x, Interval(c, b, right_open=ab.right_open))


    return All(function, limit)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(shape=(), real=True)
    Eq << apply(c > a, All[x:Interval(a, b, left_open=True)](f(x) > 0))

    e = Symbol(positive=True)
    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[1], Interval(a + e, b))

    Eq << algebra.cond.imply.infer.unbounded.apply(Eq[-1], e)

    e = Eq[-1].lhs.lhs
    Eq << Eq[-1].subs(e, c - a)

    Eq << algebra.gt.imply.gt_zero.apply(Eq[0])

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2019-07-11
