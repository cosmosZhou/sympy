from util import *


@apply
def apply(cond, cond_sum):
    fb, gb = cond.of(Equal)

    (fk, (k, a, b)), (gk, _limit) = cond_sum.of(Equal[Cup, Cup])

    assert fk._subs(k, b) == fb
    assert _limit == (k, a, b)
    assert gk._subs(k, b) == gb

    return Equal(Cup[k:a:b + 1](fk), Cup[k:a:b + 1](gk))


@prove
def prove(Eq):
    from axiom import sets
    k = Symbol.k(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(domain=Range(a + 1, oo))
    g = Function.g(etype=dtype.integer)
    f = Function.f(etype=dtype.integer)

    Eq << apply(Equal(g(b), f(b)), Equal(Cup[k:a:b](g(k)), Cup[k:a:b](f(k))))

    Eq << sets.eq.eq.imply.eq.union.apply(Eq[0], Eq[1])

#     Eq << Eq[2].this.lhs.bisect({b})

#     Eq << Eq[-1].this.rhs.bisect({b})


if __name__ == '__main__':
    run()

