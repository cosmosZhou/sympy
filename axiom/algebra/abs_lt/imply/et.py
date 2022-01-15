from util import *


@apply
def apply(lt):
    x, a = lt.of(Abs < Expr)    
    assert x.is_extended_real
    return Less(x, a), Greater(x, -a)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) < a)

    Eq << algebra.lt_abs.imply.lt.apply(Eq[0])

    Eq << algebra.lt_abs.imply.gt.apply(Eq[0])

    


if __name__ == '__main__':
    run()
# created on 2018-07-28
# updated on 2022-01-07