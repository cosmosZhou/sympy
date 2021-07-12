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
    y = Symbol.y(integer=True)
    x = Symbol.x(integer=True)
    a = Symbol.a(real=True, shape=(oo,), given=True)
    X = Symbol.X(etype=dtype.integer, finiteset=True, given=True)
    Y = Symbol.Y(etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(abs(a[y_] - Sum[x:X](a[x]) / abs(X)) <= abs(a[y_] - Sum[y:Y](a[y]) / abs(Y)), abs(Y) >= 2, Contains(y_, Y), NotContains(y_, X))

    Eq << sets.ge.imply.contains.range.apply(Eq[1])

    m = Symbol.m(domain=Range(2, oo))
    Eq << sets.contains.imply.any_eq.apply(Eq[-1], var=m)

    b = Symbol.b(shape=(oo,), integer=True)
    Eq.any_Y = Eq[-1].this.function.apply(sets.eq.imply.any_eq.condset.all, b)

    Eq << algebra.le.imply.is_nonzero.domain_definition.st.abs.apply(Eq[0])

    Eq << algebra.is_nonzero.imply.is_positive.apply(Eq[-1])

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[-1])

    Eq << sets.ge.imply.contains.range.apply(Eq[-1])

    n = Symbol.n(positive=True, integer=True)
    Eq << sets.contains.imply.any_eq.apply(Eq[-1], var=n)

    Eq << Eq[-1].this.function.apply(sets.eq.imply.any_eq.condset.all)

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1])

    Eq << algebra.any.any.imply.any_et.apply(Eq[-1], Eq.any_Y)


if __name__ == '__main__':
    run()