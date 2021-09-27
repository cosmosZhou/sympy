from util import *


@apply
def apply(given):
    n, b = given.of(Greater)    
    return Element(n, Interval(-oo, oo, right_open=False))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(extended_complex=True, given=True)
    b = Symbol(real=True, given=True)
    Eq << apply(x > b)

    Eq << Eq[-1].simplify()
    Eq << algebra.gt.given.et.strengthen.apply(Eq[-1], upper=b)


if __name__ == '__main__':
    run()