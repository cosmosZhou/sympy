from util import *


@apply
def apply(*given):
    is_positive_x, strict_less_than = given
    x = is_positive_x.of(Expr < 0)
    lhs, rhs = strict_less_than.of(Less)
    return Greater(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(x < 0, a < b)
    
    Eq << algebra.is_negative.imply.is_negative.div.apply(Eq[0])
    
    Eq << algebra.is_negative.lt.imply.gt.mul.apply(Eq[-1], Eq[1])
    
    
    
    


if __name__ == '__main__':
    run()