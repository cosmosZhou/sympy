from util import *


@apply
def apply(lt_a, lt_b):
    x, a = lt_a.of(Less)
    S[x], b = lt_b.of(Less)
    return x < Min(a, b)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x < y, x < b)

    Eq << algebra.lt_min.imply.et.lt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2022-01-03
