from util import *


@apply(given=None)
def apply(lt):
    x, a = lt.of(Less)
    return Equivalent(lt, Greater(a, x), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    Eq << apply(x < a)

    Eq << algebra.equivalent.given.et.suffice.apply(Eq[0])

    


if __name__ == '__main__':
    run()