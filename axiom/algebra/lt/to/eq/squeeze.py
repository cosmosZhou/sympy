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

    Eq << algebra.equivalent.given.et.apply(Eq[-1])

    Eq << Eq[-2].this.apply(algebra.suffice.to.ou)

    Eq << Eq[-1].this.apply(algebra.necessary.to.ou)



if __name__ == '__main__':
    run()

