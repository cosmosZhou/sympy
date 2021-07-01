from util import *


@apply
def apply(contains0, contains1, contains2):
    w, interval01 = contains0.of(Contains)
    interval01.of(Interval[0, 1])
    assert interval01.left_open and interval01.right_open    
    
    x0, S = contains1.of(Contains)    
    x1, _S = contains2.of(Contains)
    assert S == _S
    assert S.is_Interval
    
    return Contains(x0 * w + x1 * (1 - w), S)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x0 = Symbol.x0(real=True)
    x1 = Symbol.x1(real=True)
    domain = Interval(a, b, left_open=True)
    w = Symbol.w(real=True)
    Eq << apply(Contains(w, Interval(0, 1, left_open=True, right_open=True)), Contains(x0, domain), Contains(x1, domain))

    Eq.w_is_positive, Eq.w1_is_positive = sets.contains.imply.et.split.interval.apply(Eq[0])

    Eq.w1_is_positive = -Eq.w1_is_positive + 1

    Eq << sets.is_positive.contains.imply.contains.mul.apply(Eq.w_is_positive, Eq[1])

    Eq << sets.is_positive.contains.imply.contains.mul.apply(Eq.w1_is_positive, Eq[2])

    Eq << sets.contains.contains.imply.contains.interval.add.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)


if __name__ == '__main__':
    run()