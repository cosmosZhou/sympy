from util import *
import axiom



@apply
def apply(given):
    x = axiom.is_positive(given)

    return 1 / x > 0


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(x + y > 0)

    Eq << algebra.is_positive.imply.is_positive.div.apply(Eq[-1])

if __name__ == '__main__':
    run()
