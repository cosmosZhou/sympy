from util import *


@apply
def apply(lt, all_gt, limit_is_real_fx, limit_is_real_gx):
    a, b = lt.of(Less)
    (lhs, rhs), (x, domain) = all_gt.of(All[Greater])
    _a, _b = domain.of(Interval)
    assert a == _a and b == _b

    (_lhs, (x, x0, dir)), R = limit_is_real_fx.of(Element[Limit])
    assert _lhs == lhs
    assert R in Reals
    (_rhs, limit), R = limit_is_real_gx.of(Element[Limit])
    assert _rhs == rhs
    assert R in Reals
    assert limit == (x, x0, dir)

    assert lhs.is_continuous(x, domain)
    assert rhs.is_continuous(x, domain)
    if dir < 0:
        x0 = b
        assert domain.right_open
    elif dir > 0:
        x0 = a
        assert domain.left_open

    return GreaterEqual(Limit[x:x0:dir](lhs), Limit[x:x0:dir](rhs))


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    domain = Interval(a, b, right_open=True)
    f, g = Function(real=True, continuous=domain)
    Eq << apply(a < b, All[x:domain](Greater(f(x), g(x))), Element(Limit[x:b:-1](f(x)), Reals), Element(Limit[x:b:-1](g(x)), Reals))



    Eq <<= calculus.imply.is_continuous.interval.apply(f(x), (x, domain)), calculus.imply.is_continuous.interval.apply(g(x), (x, domain))

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.expr.apply(calculus.eq_limit.eq_limit.imply.eq_limit.sub)

    xi = Eq[-1].variable
    Eq <<= Eq[1].this.expr.apply(algebra.gt.imply.gt_zero)

    Eq <<= Eq[-1].limits_subs(x, xi)

    Eq <<= Eq[-1] & Eq[-2]

    Eq <<= Eq[-1].this.expr.apply(algebra.eq.gt.imply.gt.subs)

    Eq <<= algebra.all.imply.infer.apply(Eq[-1])

    epsilon = Symbol(positive=True)
    Eq <<= Eq[-1].subs(xi, b - epsilon)

    Eq <<= Eq[-1].this.lhs.apply(sets.el.given.el.neg)

    Eq <<= Eq[-1].this.lhs.apply(sets.el.given.el.add, b)

    Eq <<= Eq[-1].this.lhs.apply(sets.el_interval.given.et)

    Eq << algebra.infer.imply.all.apply(Eq[-1])

    Eq << algebra.lt.imply.gt_zero.apply(Eq[0])

    Eq << calculus.gt_zero.all_gt_zero.imply.limit_ge_zero.st.limit.apply(Eq[-1], Eq[-2])

    Eq << calculus.is_limited.is_limited.imply.eq.algebraic_limit_theorem.sub.apply(Eq[2], Eq[3])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << sets.ge.el.imply.ge.add.apply(Eq[-1], Eq[3])


if __name__ == '__main__':
    run()
# created on 2020-06-26
