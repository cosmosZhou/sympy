from util import *


@apply
def apply(contains1, contains2):
    x0, S0 = contains1.of(Contains)    
    x1, S1 = contains2.of(Contains)
    
    assert S0.is_Interval and S1.is_Interval
    assert S0.left_open == S1.left_open
    assert S0.right_open == S1.right_open
        
    return Contains(x0 + x1, S0 + S1)


@prove
def prove(Eq):
    from axiom import sets

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)
    d = Symbol.d(real=True)
    x0 = Symbol.x0(real=True)
    x1 = Symbol.x1(real=True)
    Eq << apply(Contains(x0, Interval(a, b, left_open=True)), Contains(x1, Interval(c, d, left_open=True)))

    Eq << sets.contains.imply.et.split.interval.apply(Eq[0])

    Eq << sets.contains.imply.et.split.interval.apply(Eq[1])

    Eq <<= Eq[-2] + Eq[-4], Eq[-1] + Eq[-3]

    Eq << sets.gt.le.imply.contains.interval.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()