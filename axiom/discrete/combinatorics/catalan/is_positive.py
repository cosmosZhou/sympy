from util import *


def is_catalan_series(*given):
    C0_definition, Cn1_definition = given

    C0, one = C0_definition.of(Equal)
    assert one.is_One

    Cn1, summation = Cn1_definition.of(Equal)
    fk, (k, zero, n1) = summation.of(Sum)

    n = n1 - 1
    assert zero.is_zero

    Cn = Cn1._subs(n, n - 1)
    assert Cn._subs(n, 0) == C0

    Cnk, Ck = fk.of(Mul)
    assert Ck == Cn._subs(n, k)
    assert Cnk == Cn._subs(n, n - k)
    return Cn, n


@apply
def apply(*given):
    Cn, n = is_catalan_series(*given)
    return Greater(Cn, 0)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True, given=False)
    C = Symbol.C(shape=(oo,), integer=True)
    Eq << apply(Equal(C[0], 1),
                Equal(C[n + 1], Sum[k:n + 1](C[k] * C[n - k])))

    Eq.initial = algebra.eq.imply.gt.apply(Eq[0], 0)

    k = Symbol.k(domain=Range(0, n + 1))
    Eq.induct = Eq[2].subs(n, n + 1)

    Eq.hypothsis_k = Eq[2].subs(n, k)

    Eq.hypothsis_nk = algebra.cond.imply.cond.subs.apply(Eq.hypothsis_k, k, n - k)

    Eq << Eq.hypothsis_nk * Eq.hypothsis_k

    Eq << algebra.gt.imply.gt.sum.apply(Eq[-1], (k,))

    Eq << Eq[-1].this.lhs.limits_subs(k, k.copy(domain=None))

    Eq << Eq[-1].this.lhs.subs(Eq[1].reversed)

    Eq << Suffice(Eq.hypothsis_k, Eq.induct, plausible=True)

    Eq << Eq[-1].this.lhs.forall((k,))

    Eq << algebra.cond.suffice.imply.cond.induct.second.split.all.apply(Eq.initial, Eq[-1], n=n)

    Eq << Eq[2].subs(n, k)


if __name__ == '__main__':
    run()

