from util import *


@apply
def apply(*given):
    for i, cond in enumerate(given):
        if cond.is_All:            
            all_is_positive = cond
            
            given = [*given]
            del given[i]
            break            
    
    (fx, (x_, d)), (x__, domain) = all_is_positive.of(All[Derivative > 0])
    assert domain.left_open and domain.right_open
    assert d == 2
    assert x_ == x__
    
    for i, cond in enumerate(given):
        w, interval = cond.of(Contains)
        if interval != domain:
            assert interval in Interval(0, 1)            
            del given[i]
            break
            
    contains0, contains1 = given
    x0, _domain = contains0.of(Contains)
    x1, __domain = contains1.of(Contains)
    assert domain == _domain == __domain
        
    return GreaterEqual(w * fx._subs(x_, x0) + (1 - w) * fx._subs(x_, x1), fx._subs(x_, w * x0 + (1 - w) * x1))


@prove
def prove(Eq):
    from axiom import algebra, calculus

    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(real=True)
    w = Symbol.w(real=True)
    f = Function.f(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    x0 = Symbol.x0(real=True)
    x1 = Symbol.x1(real=True)
    Eq << apply(Contains(w, Interval(0, 1, right_open=True)), Contains(x0, domain), Contains(x1, domain), All[x:domain](Derivative(f(x), (x, 2)) > 0))

    w_ = Symbol.w(domain=Eq[0].rhs)
    x_ = Symbol.x(domain=domain)
    Eq << algebra.all.imply.cond.subs.apply(Eq[3], x, x_)

    Eq << calculus.is_positive.imply.ge.Jesson.apply(Eq[-1], w=w_)

    Eq << algebra.cond.imply.all.apply(Eq[-1], w_)

    Eq << algebra.all.imply.suffice.apply(Eq[-1])

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])

    x0 = Eq[-1].lhs.find(f).arg
    Eq << algebra.cond.imply.all.apply(Eq[-1], x0)

    Eq << algebra.all.imply.suffice.apply(Eq[-1])

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[1], Eq[-1])

    x1 = Eq[-1].lhs.find(Add * ~f).arg
    Eq << algebra.cond.imply.all.apply(Eq[-1], x1)

    Eq << algebra.all.imply.suffice.apply(Eq[-1])
    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[2], Eq[-1])


if __name__ == '__main__':
    run()