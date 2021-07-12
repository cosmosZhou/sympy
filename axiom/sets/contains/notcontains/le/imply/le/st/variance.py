from util import *


@apply
def apply(le, contains, notcontains):
    y_, Y = contains.of(Contains)
    ___y_, __X = notcontains.of(NotContains)

    ((a, _y_), (((_a, _x), (x, X)), _X)), ((__a, __y_), (((___a, y), (_y, _Y)), __Y))= le.of(Abs[Indexed - Sum[Indexed] / Abs] <= Abs[Indexed - Sum[Indexed] / Abs])
    
    assert a == _a == __a == ___a
    assert X == _X == __X and x == _x
    assert y_ == _y_ == __y_ == ___y_
    assert Y == _Y == _Y and y == _y

    X_ = X | {y_}
    Y_ = Y - {y_}
    return LessEqual(Sum[x:X_]((a[x] - (Sum[x:X_](a[x])) / (abs(X) + 1)) ** 2) + Sum[y:Y_]((a[y] - Sum[y:Y_](a[y]) / (abs(Y) - 1)) ** 2),
                     Sum[x:X]((a[x] - (Sum[x:X](a[x])) / abs(X)) ** 2) + Sum[y:Y]((a[y] - Sum[y:Y](a[y]) / abs(Y)) ** 2))


@prove
def prove(Eq):
    from axiom import algebra, sets

    y_ = Symbol("y'", integer=True, given=True)
    y = Symbol.y(integer=True)
    x = Symbol.x(integer=True)
    a = Symbol.a(real=True, shape=(oo,), given=True)
    X = Symbol.X(etype=dtype.integer, finiteset=True, given=True)
    Y = Symbol.Y(etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(abs(a[y_] - Sum[x:X](a[x]) / abs(X)) <= abs(a[y_] - Sum[y:Y](a[y]) / abs(Y)), Contains(y_, Y), NotContains(y_, X))

    Eq.eq, Eq.ne = algebra.cond.given.suffice.split.apply(Eq[-1], cond=Equal(abs(Y), 1))

    Eq.suffice_et = algebra.cond.imply.suffice.et.apply(Eq[1], cond=Eq.eq.lhs)

    Eq << Eq.suffice_et.this.rhs.apply(sets.eq.contains.imply.is_emptyset)

    Eq <<= Eq.eq & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.eq)

    Eq << algebra.suffice.given.et.suffice.apply(Eq[-1])

    Eq.suffice_eq = Eq.suffice_et.this.rhs.apply(sets.eq.contains.imply.eq.finiteset)

    Eq <<= Eq.suffice_eq & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.eq)

    Eq << algebra.suffice.given.et.suffice.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.le.given.eq)

    Eq << algebra.cond.imply.suffice.apply(Eq[0], cond=Eq[-1].lhs)

    Eq <<= Eq[-1] & Eq.suffice_eq

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.imply.cond.subs)

    Eq << Eq[-1].this.rhs.apply(algebra.abs_is_nonpositive.imply.is_zero)

    Eq << algebra.cond.imply.suffice.apply(Eq[2], cond=Eq[-1].lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(sets.eq.notcontains.imply.eq.st.variance)

    Eq << sets.notcontains.imply.eq.abs.apply(Eq[2])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << sets.contains.imply.ge.abs.apply(Eq[1])

    Eq << algebra.cond.imply.suffice.et.apply(Eq[-1], cond=Eq.ne.lhs)

    Eq << Eq[-1].this.rhs.apply(algebra.gt.imply.ge.strengthen)

    Eq << algebra.cond.imply.suffice.apply(Eq[0] & Eq[1] & Eq[2], cond=Eq.ne.lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(sets.le.ge.contains.notcontains.imply.le.st.variance)


if __name__ == '__main__':
    run()
