from util import *



@apply(given=None)
def apply(given):
    x, a = given.of(LessEqual)
    assert x >= a
    return Equivalent(given, Equal(x, a))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(domain=Interval(1, oo))

    Eq << apply(LessEqual(x, 1))

    Eq << algebra.iff.given.et.apply(Eq[-1])

    Eq << Eq[-2].this.apply(algebra.infer.to.ou)

    Eq << Eq[-1].apply(algebra.assuming.given.ou)


if __name__ == '__main__':
    run()

# created on 2019-11-26
# updated on 2019-11-26
