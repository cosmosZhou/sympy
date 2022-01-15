from util import *


@apply
def apply(ge_a, ge_b):
    x, a = ge_a.of(GreaterEqual)
    S[x], b = ge_b.of(GreaterEqual)
    return x >= Max(a, b)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x >= y, x >= b)

    Eq << algebra.ge_max.imply.et.ge.apply(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2022-01-03
