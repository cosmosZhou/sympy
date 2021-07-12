from util import *


@apply
def apply(eq):
    (a, y), (((_a, _x), (x, X)), _X) = eq.of(Equal[Indexed, Sum[Indexed] / Abs])

    assert a == _a
    assert X == _X and x == _x

    X_ = X | {y}
    return Equal(Sum[x:X_]((a[x] - (Sum[x:X_](a[x])) / (abs(X_))) ** 2),
                 Sum[x:X]((a[x] - (Sum[x:X](a[x])) / abs(X)) ** 2))


@prove
def prove(Eq):
    from axiom import algebra, sets

    y = Symbol.y(integer=True, given=True)
    x = Symbol.x(integer=True)
    a = Symbol.a(real=True, shape=(oo,), given=True)
    X = Symbol.X(etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(Equal(a[y], Sum[x:X](a[x]) / abs(X)))

    Eq << algebra.cond.given.suffice.split.apply(Eq[1], cond=Contains(y, X))

    Eq << Contains(y, X).this.apply(sets.contains.imply.eq.union)

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.eq)

    Eq << algebra.cond.imply.suffice.apply(Eq[0], cond=Eq[3].lhs)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(sets.eq.notcontains.imply.eq.st.variance)


if __name__ == '__main__':
    run()