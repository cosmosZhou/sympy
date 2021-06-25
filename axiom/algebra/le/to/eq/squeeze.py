from util import *



@apply(given=None)
def apply(given):
    x, a = given.of(LessEqual)
    assert x >= a
    return Equivalent(given, Equal(x, a))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(domain=Interval(1, oo))

    Eq << apply(LessEqual(x, 1))

    Eq << algebra.equivalent.given.cond.apply(Eq[-1])

    Eq << Eq[-2].this.apply(algebra.suffice.to.ou)

    Eq << Eq[-1].apply(algebra.necessary.given.ou)


if __name__ == '__main__':
    run()

