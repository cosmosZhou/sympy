from util import *


@apply
def apply(*given):
    for cond in given:
        if cond.is_LessEqual:
            le = cond
        elif cond.is_GreaterEqual:
            ge = cond
        elif cond.is_Contains:
            contains = cond
        elif cond.is_NotContains:
            notcontains = cond

    ((a, _y_), (((_a, _x), (x, X)), _X)), ((__a, __y_), (((___a, y), (_y, _Y)), __Y))= le.of(Abs[Indexed - Sum[Indexed] / Abs] <= Abs[Indexed - Sum[Indexed] / Abs])
    ___Y = ge.of(Abs >= 2)
    y_, Y = contains.of(Contains)
    ___y_, __X = notcontains.of(NotContains)

    assert a == _a == __a == ___a
    assert X == _X == __X and x == _x
    assert y_ == _y_ == __y_ == ___y_
    assert Y == _Y == __Y == ___Y and y == _y

    X_ = X | {y_}
    Y_ = Y - {y_}
    return LessEqual(Sum[x:X_]((a[x] - (Sum[x:X_](a[x])) / (abs(X) + 1)) ** 2) + Sum[y:Y_]((a[y] - Sum[y:Y_](a[y]) / (abs(Y) - 1)) ** 2),
                     Sum[x:X]((a[x] - (Sum[x:X](a[x])) / abs(X)) ** 2) + Sum[y:Y]((a[y] - Sum[y:Y](a[y]) / abs(Y)) ** 2))


@prove
def prove(Eq):
    from axiom import sets, algebra

    y_ = Symbol("y'", integer=True, given=True)
    y = Symbol(integer=True)
    x = Symbol(integer=True)
    t = Symbol(real=True, shape=(oo,), given=True)
    X = Symbol(etype=dtype.integer, finiteset=True, given=True)
    Y = Symbol(etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(abs(t[y_] - Sum[x:X](t[x]) / abs(X)) <= abs(t[y_] - Sum[y:Y](t[y]) / abs(Y)), abs(Y) >= 2, Contains(y_, Y), NotContains(y_, X))

    b = Symbol(shape=(oo,), integer=True)
    Eq << sets.ge_abs.imply.any_eq.apply(Eq[1], b)

    Eq << algebra.le.imply.is_nonzero.domain_definition.st.abs.apply(Eq[0])

    a = Symbol(shape=(oo,), integer=True)
    Eq << sets.abs_is_nonzero.imply.any_eq.apply(Eq[-1], a)

    Eq.any_et = algebra.any.any.imply.any_et.apply(Eq[-1], Eq[-3], simplify=None)

    Eq.abs_complement = sets.contains.imply.eq.abs.complement.apply(Eq[2])

    Eq << algebra.eq.ge.imply.ge.subs.apply(Eq.abs_complement, Eq[1])

    b_ = Symbol("b'", shape=(oo,), integer=True)
    Eq << sets.ge_abs.imply.any_eq.apply(Eq[-1], b_)

    Eq << Eq[-1].subs(Eq.abs_complement)

    Eq.abs_union = sets.notcontains.imply.eq.abs.apply(Eq[3])

    Eq << algebra.eq.imply.is_positive.apply(Eq.abs_union)

    a_ = Symbol("a'", shape=(oo,), integer=True)
    Eq << sets.abs_is_positive.imply.any_eq.apply(Eq[-1], a_)
    Eq << Eq[-1].subs(Eq.abs_union)

    Eq << algebra.any.any.imply.any_et.apply(Eq[-1], Eq[-4], simplify=None)

    Eq << algebra.any.any.imply.any_et.apply(Eq.any_et, Eq[-1], simplify=None)

    Eq << algebra.cond.any.imply.any_et.apply(Eq[0] & Eq[3], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(sets.eq_cup.eq_cup.eq_cup.eq_cup.le.notcontains.imply.le)


if __name__ == '__main__':
    run()