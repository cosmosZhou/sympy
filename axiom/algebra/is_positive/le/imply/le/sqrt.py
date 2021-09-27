from util import *


@apply
def apply(is_positive, lt):
    x = is_positive.of(Expr > 0)
    _x, M = lt.of(LessEqual)
    assert x == _x

    return LessEqual(sqrt(x), sqrt(M))


@prove
def prove(Eq):
    from axiom import algebra
    
    x, M = Symbol(real=True)
    Eq << apply(x > 0, x <= M)
    
    Eq << algebra.is_positive.imply.is_nonnegative.apply(Eq[0])
    Eq << algebra.is_nonnegative.le.imply.le.sqrt.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()