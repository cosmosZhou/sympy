from util import *


@apply
def apply(given, old, new):
    import axiom
    function, *limits = given.of(ForAll)
    assert given.is_ForAll
    n, a, b = axiom.limit_is_Interval(limits, integer=True)
    assert old == n
    m = new + n + 1
    assert m == a + b
    return ForAll[n:m - b:m - a](function._subs(old, new))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True)
    m = Symbol.m(integer=True)
    f = Function.f(integer=True)

    Eq << apply(ForAll[n:0:m + 1](f(n) > 0), n, m - n)

    Eq << algebra.all.imply.ou.subs.apply(Eq[0], n, m - n)

    Eq << Eq[-1].this.args[1].apply(sets.notcontains.imply.notcontains.neg)

    Eq << Eq[-1].this.args[0].apply(sets.notcontains.imply.notcontains.add, m)

    Eq << algebra.ou.imply.all.apply(Eq[-1], pivot=1, wrt=n)


if __name__ == '__main__':
    run()

