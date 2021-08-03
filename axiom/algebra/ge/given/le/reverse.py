from util import *


@apply
def apply(ge):
    x, a = ge.of(GreaterEqual)
    return LessEqual(a, x)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    Eq << apply(x >= a)

    Eq << algebra.le.imply.ge.reverse.apply(Eq[1])

    


if __name__ == '__main__':
    run()