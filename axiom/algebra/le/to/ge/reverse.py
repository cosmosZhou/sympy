from util import *


@apply(given=None)
def apply(ge):
    x, a = ge.of(LessEqual)
    return Equivalent(ge, GreaterEqual(a, x), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(x <= a)

    Eq << algebra.equivalent.given.et.suffice.apply(Eq[0])


if __name__ == '__main__':
    run()
