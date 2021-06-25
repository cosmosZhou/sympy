from util import *


@apply
def apply(is_positive, contains):
    a = is_positive.of(Expr < 0)
    fa, R = contains.of(Contains)
    assert R.is_Interval
    return Contains(fa * a, Interval(R.stop * a, R.start * a, left_open=R.right_open, right_open=R.left_open))


@prove
def prove(Eq):
    from axiom import sets, algebra
    t = Symbol.t(real=True)
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(t < 0, Contains(x, Interval(a, b, left_open=True)))
    
    Eq << sets.contains.imply.et.split.interval.apply(Eq[1])
    
    Eq << algebra.et.imply.conds.apply(Eq[-1])
    
    Eq <<= algebra.is_negative.gt.imply.lt.mul.apply(Eq[0], Eq[-2]), algebra.is_negative.le.imply.ge.mul.apply(Eq[0], Eq[-1])
    
    Eq << sets.lt.ge.imply.contains.interval.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()