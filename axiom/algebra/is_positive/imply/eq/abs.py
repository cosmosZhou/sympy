from util import *
import axiom



@apply
def apply(given):
    x = axiom.is_positive(given)
    return Equal(abs(x), x)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)

    Eq << apply(x > 0)

    Eq << algebra.gt.imply.ge.relax.apply(Eq[0])

    Eq << algebra.is_nonnegative.imply.eq.abs.apply(Eq[-1])


if __name__ == '__main__':
    run()
