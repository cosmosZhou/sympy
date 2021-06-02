from util import *


def absorb_back(Sum, Equal, *imply, criteria=None):
    import axiom
    cond, cond_sum = imply

    assert isinstance(cond, Equal)
    fb, gb = cond.args

    assert isinstance(cond_sum, Equal)
    fx_sum, gx_sum = cond_sum.args

    assert isinstance(fx_sum, Sum)
    fk, *limits = fx_sum.args

    k, a, b = axiom.limit_is_Interval(limits)
    assert fk._subs(k, b) == fb

    assert isinstance(gx_sum, Sum)
    gk, *_limits = gx_sum.args

    assert _limits == limits
    assert gk._subs(k, b) == gb

    if criteria:
        assert criteria(cond)
        assert criteria(cond_sum)

    return Equal(Sum[k:a:b + 1](fk), Sum[k:a:b + 1](gk))


@apply
def apply(*imply):
    return absorb_back(Sum, Equal, *imply)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(domain=Range(a + 1, oo))
    g = Function.g(integer=True)
    f = Function.f(integer=True)

    Eq << apply(Equal(g(b), f(b)), Equal(Sum[k:a:b](g(k)), Sum[k:a:b](f(k))))

    Eq << algebra.eq.eq.imply.eq.add.apply(Eq[0], Eq[1])

    Eq << Eq[2].this.lhs.split({b})

    Eq << Eq[-1].this.rhs.split({b})


if __name__ == '__main__':
    run()

