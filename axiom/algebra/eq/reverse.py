from util import *


@apply(given=None)
def apply(eq):
    a, b = eq.of(Equal)
    return Equivalent(eq, Equal(b, a), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    b = Symbol.b(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    Eq << apply(Equal(a, b))

    Eq << algebra.equivalent.given.et.suffice.apply(Eq[0])


if __name__ == '__main__':
    run()