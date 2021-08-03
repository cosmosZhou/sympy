from util import *


@apply
def apply(given):
    p, q = given.of(Equal)
    if not p.is_Bool:
        p, q = q, p

    p = p.of(Bool)
    _p, q = q.of(Mul)
    _p = _p.of(Bool)
    q = q.of(Bool)
    if p != _p:
        _p, q = q, _p
    assert p == _p

    return Suffice(p, q)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True)
    f = Symbol.f(integer=True, shape=(oo,))
    h = Symbol.h(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))

    Eq << apply(Equal(Bool(Equal(f[n], g[n])), Bool(Equal(f[n], g[n])) * Bool(Equal(f[n + 1], g[n + 1]))))

    Eq << Eq[0] - Eq[0].rhs

    Eq << Eq[-1].this.lhs.collect(Eq[0].lhs)

    Eq << algebra.mul_is_zero.imply.ou.is_zero.apply(Eq[-1])

    Eq << Eq[-1].this.args[1].apply(algebra.is_zero.imply.ne, One())

    Eq << algebra.ou.imply.suffice.apply(Eq[-1], pivot=1)

    Eq << Eq[-1].this.lhs.lhs.apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.rhs.lhs.apply(algebra.bool.to.piecewise)


if __name__ == '__main__':
    run()
