from util import *

@apply
def apply(contains0, contains1, contains2):
    w, interval01 = contains0.of(Contains)
    assert interval01 in Interval(0, 1)

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
    Eq << apply(Contains(w, Interval(0, 1)), Contains(x0, domain), Contains(x1, domain))

    w = Symbol.w(domain=Eq[0].rhs)
    Eq << sets.contains.contains.imply.contains.interval.apply(Eq[1], Eq[2], w=w)

    Eq << Eq[-1].forall((w,))

    Eq << algebra.all.imply.suffice.apply(Eq[-1])

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
from . import open
