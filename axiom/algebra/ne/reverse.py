from util import *


@apply(given=None)
def apply(ne):
    a, b = ne.of(Unequal)
    return Equivalent(ne, Unequal(b, a), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    b = Symbol.b(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    Eq << apply(Unequal(a, b))

    Eq << algebra.equivalent.given.et.suffice.apply(Eq[0])

    


if __name__ == '__main__':
    run()