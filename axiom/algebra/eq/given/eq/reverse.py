from util import *


@apply
def apply(eq):
    a, b = eq.of(Equal)
    return Equal(b, a)


@prove
def prove(Eq):
    from axiom import algebra

    b = Symbol.b(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    Eq << apply(Equal(a, b))

    Eq << algebra.eq.imply.eq.reverse.apply(Eq[1])

    


if __name__ == '__main__':
    run()