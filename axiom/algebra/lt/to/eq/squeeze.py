from util import *



@apply(given=None)
def apply(given):
    x, a = given.of(Less)
    assert x.is_integer and a.is_integer
    a -= 1

    assert x >= a
    return Equivalent(given, Equal(x, a))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(domain=Range(1, oo))

    Eq << apply(Less(x, 2))

    Eq << algebra.iff.given.et.apply(Eq[-1])

    Eq << Eq[-2].this.apply(algebra.infer.to.ou)

    Eq << Eq[-1].this.apply(algebra.assuming.to.ou)



if __name__ == '__main__':
    run()

# created on 2020-01-10
# updated on 2020-01-10
