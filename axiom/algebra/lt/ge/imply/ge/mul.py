from util import *


@apply
def apply(lt, ge):
    a, b = lt.of(Less)
    x, y = ge.of(GreaterEqual)
    z = b - a
    return GreaterEqual(z * x,  z * y)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, x, y = Symbol(real=True)
    Eq << apply(a < b, x >= y)

    Eq << algebra.lt.imply.is_positive.apply(Eq[0])

    Eq << algebra.is_positive.ge.imply.ge.mul.apply(Eq[-1], Eq[1])




if __name__ == '__main__':
    run()
