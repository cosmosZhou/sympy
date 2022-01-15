from util import *


@apply
def apply(le):
    abs_x, a = le.of(LessEqual)
    x = abs_x.of(Abs)
    return LessEqual(x, a), GreaterEqual(x, -a)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(integer=True, given=True)
    Eq << apply(abs(x) <= a)

    Eq << algebra.le.le.imply.le.abs.apply(Eq[1], -Eq[2])

    

    


if __name__ == '__main__':
    run()
# created on 2022-01-07
