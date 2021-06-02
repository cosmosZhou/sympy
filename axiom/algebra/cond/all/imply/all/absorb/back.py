from util import *


@apply
def apply(*imply):
    import axiom
    cond, forall = imply
    fn, *limits = forall.of(ForAll)
    k, a, b = axiom.limit_is_Interval(limits)
    assert fn._subs(k, b) == cond

    return ForAll[k:a:b + 1](fn)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(domain=Range(a + 1, oo))
    g = Function.g(integer=True)

    Eq << apply((g(b) > 0), ForAll[k:a:b](g(k) > 0))

    Eq << algebra.all.given.et.apply(Eq[-1], cond={b})

    Eq << algebra.et.given.conds.apply(Eq[-1])


if __name__ == '__main__':
    run()

