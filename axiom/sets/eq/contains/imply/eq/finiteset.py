from util import *


@apply
def apply(equal, contains):
    if contains.is_Equal:
        contains, equal = equal, contains

    a, A = contains.of(Contains)

    _A = equal.of(Equal[Abs, 1])
    assert _A == A
    return Equal(A, a.set, evaluate=False)


@prove
def prove(Eq):
    from axiom import sets, algebra

    A = Symbol.A(etype=dtype.integer, given=True)
    a = Symbol.a(integer=True, given=True)
    Eq << apply(Equal(abs(A), 1), Contains(a, A))

    Eq << sets.eq.imply.any_eq.one.apply(Eq[0], reverse=True)

    Eq << algebra.cond.any.imply.any_et.apply(Eq[1], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.cond.cond.imply.et, algebra.eq.cond.imply.cond.subs, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.imply.eq.subs, swap=True, reverse=True)


if __name__ == '__main__':
    run()