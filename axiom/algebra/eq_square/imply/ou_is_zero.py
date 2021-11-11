from util import *


@apply
def apply(eq):
    a, b = eq.of(Equal[Expr ** 2, Expr])
    _b = b.of(Expr ** 2)
    if _b is None:
        _b = sqrt(b)    
        
        
    return Equal(a - _b, 0) | Equal(a + _b, 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(complex=True, given=True)
    Eq << apply(Equal(a ** 2, b ** 2))

    Eq << algebra.ou_is_zero.given.mul_is_zero.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add, deep=True).reversed


if __name__ == '__main__':
    run()
# created on 2018-11-13
# updated on 2018-11-13
