from util import *


@apply
def apply(given):
    x, y = given.of(Greater)
    return Equal(abs(x - y), x - y)


@prove
def prove(Eq):
    from axiom import algebra
    
    x, y = Symbol(real=True)
    Eq << apply(x > y)
    
    Eq << algebra.gt.imply.is_positive.apply(Eq[0])
    Eq << algebra.is_positive.imply.eq.abs.apply(Eq[-1])


if __name__ == '__main__':
    run()