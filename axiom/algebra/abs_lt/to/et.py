from util import *


@apply(given=None)
def apply(lt):
    x, a = lt.of(Abs < Expr)    
    assert x.is_extended_real
    return Equivalent(lt, And(Less(x, a), Greater(x, -a)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) < a)

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.abs_lt.imply.et)

    Eq << Eq[-1].this.lhs.apply(algebra.abs_lt.given.et)

    


if __name__ == '__main__':
    run()
# created on 2022-01-07
