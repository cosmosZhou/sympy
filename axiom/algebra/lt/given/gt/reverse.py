from util import *


@apply
def apply(lt):
    x, a = lt.of(Less)
    return Greater(a, x)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    Eq << apply(x < a)

    Eq << algebra.gt.imply.lt.reverse.apply(Eq[1])

    


if __name__ == '__main__':
    run()