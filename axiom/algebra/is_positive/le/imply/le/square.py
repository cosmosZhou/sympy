from util import *


@apply
def apply(is_positive, le):
    x = is_positive.of(Expr > 0)
    _x, M = le.of(LessEqual)
    assert x == _x

    return LessEqual(x * x, M * M)


@prove
def prove(Eq):
    from axiom import algebra

    x, M = Symbol(real=True)
    Eq << apply(x > 0, x <= M)

    Eq << algebra.gt.imply.ge.relax.apply(Eq[0])

    Eq << algebra.is_nonnegative.le.imply.le.square.apply(Eq[-1], Eq[1])

    

    

    

    


if __name__ == '__main__':
    run()