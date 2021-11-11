from util import *


@apply
def apply(given):
    x, b = given.of(Equal)
    domain = x.domain
    a, b1 = domain.of(Range)
    assert b1 == b + 1

    return GreaterEqual(x, b)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol(integer=True)
    b = Symbol(integer=True, given=True)
    x = Symbol(domain=Range(a, b + 1), given=True)
    Eq << apply(Equal(x, b))

    Eq << algebra.ge.imply.eq.squeeze.range.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2019-03-31
# updated on 2019-03-31
