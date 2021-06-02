from util import *


@apply
def apply(*imply):
    import axiom
    cond, cond_sum = imply
    fa, ga = cond.of(Equal)

    fx_sum, gx_sum = cond_sum.of(Equal)

    fk, *limits = fx_sum.of(Cup)
    k, a, b = axiom.limit_is_Interval(limits)
    assert fk._subs(k, a - 1) == fa

    gk, *_limits = gx_sum.of(Cup)
    assert _limits == limits
    assert gk._subs(k, a - 1) == ga

    return Equal(Cup[k:a - 1:b](fk), Cup[k:a - 1:b](gk))


@prove
def prove(Eq):
    from axiom import sets
    k = Symbol.k(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(domain=Range(a + 1, oo))
    g = Function.g(etype=dtype.integer)
    f = Function.f(etype=dtype.integer)

    Eq << apply(Equal(g(a - 1), f(a - 1)), Equal(Cup[k:a:b](g(k)), Cup[k:a:b](f(k))))

    Eq << sets.eq.eq.imply.eq.union.apply(Eq[0], Eq[1])

#     Eq << Eq[2].this.lhs.bisect({a - 1})

#     Eq << Eq[-1].this.rhs.bisect({a - 1})


if __name__ == '__main__':
    run()

