from util import *


@apply
def apply(is_positive, contains):
    a = is_positive.of(Expr > 0)
    fa, R = contains.of(Contains)
    assert R.is_Interval
    start = R.start
    if not start.is_infinite:
        start *= a
        
    stop = R.stop
    if not stop.is_infinite:
        stop *= a        
        
    return Contains(fa * a, R.copy(start=start, stop=stop))


@prove
def prove(Eq):
    from axiom import sets, algebra

    t = Symbol.t(real=True)
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(t > 0, Contains(x, Interval(a, b, left_open=True)))

    Eq << sets.contains.imply.et.split.interval.apply(Eq[1])

    Eq << algebra.et.imply.conds.apply(Eq[-1])

    Eq <<= algebra.is_positive.gt.imply.gt.mul.apply(Eq[0], Eq[-2]), algebra.is_positive.le.imply.le.mul.apply(Eq[0], Eq[-1])

    Eq << sets.gt.le.imply.contains.interval.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()