from util import *


@apply
def apply(given, var=None):
    S, n = given.of(Equal[Abs])

    assert n.is_extended_positive
    if var is None:
        var = S.element_symbol()
    return Any[var:S](Equal(abs(S - var.set), n - 1))


@prove
def prove(Eq):
    from axiom import sets, algebra
    S = Symbol.S(etype=dtype.integer)
    n = Symbol.n(integer=True, positive=True)

    Eq << apply(Equal(abs(S), n))

    Eq << algebra.eq.imply.ge.apply(Eq[0])

    Eq << sets.ge.imply.any_contains.apply(Eq[-1], simplify=False)

    Eq << sets.any_contains.imply.any_contains.limits_restricted.apply(Eq[-1], simplify=False)

    i = Eq[-1].expr.lhs
    Eq << sets.imply.eq.principle.addition.apply(S, i.set)

    Eq << Eq[-2].this.expr.apply(sets.contains.imply.eq.union)

    Eq << algebra.any_eq.cond.imply.any.subs.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.expr - 1

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

