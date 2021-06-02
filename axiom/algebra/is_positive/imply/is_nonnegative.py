from util import *
import axiom



@apply
def apply(given):
    x = axiom.is_positive(given)
    return GreaterEqual(x, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)

    Eq << apply(x > 0)

    Eq << algebra.gt.imply.ge.relax.apply(Eq[0])


if __name__ == '__main__':
    run()

