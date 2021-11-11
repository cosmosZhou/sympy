from util import *


@apply
def apply(given):
    abs_x, a = given.of(Less)
    x = abs_x.of(Abs)
    assert x.is_extended_real
    return Less(x, a)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) < a)

    Eq << algebra.imply.le.abs.apply(x)

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[-1], Eq[0])

    

    

    

    


if __name__ == '__main__':
    run()
# created on 2018-07-27
# updated on 2018-07-27
