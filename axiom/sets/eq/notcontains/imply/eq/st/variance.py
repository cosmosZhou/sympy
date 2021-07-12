from util import *


@apply
def apply(notcontains, eq):
    if notcontains.is_Equal:
        notcontains, eq = eq, notcontains
    _y, __X = notcontains.of(NotContains)
    (a, y), (((_a, _x), (x, X)), _X) = eq.of(Equal[Indexed, Sum[Indexed] / Abs])

    assert a == _a
    assert y == _y
    assert X == _X  == __X and x == _x

    X_ = X | {y}
    return Equal(Sum[x:X_]((a[x] - (Sum[x:X_](a[x])) / (abs(X_))) ** 2),
                 Sum[x:X]((a[x] - (Sum[x:X](a[x])) / abs(X)) ** 2))


@prove
def prove(Eq):
    from axiom import sets, algebra

    y = Symbol.y(integer=True, given=True)
    x = Symbol.x(integer=True)
    a = Symbol.a(real=True, shape=(oo,), given=True)
    X = Symbol.X(etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(NotContains(y, X), Equal(a[y], Sum[x:X](a[x]) / abs(X)))

    Eq << sets.notcontains.imply.eq.abs.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << sets.notcontains.imply.eq.sum.apply(Eq[0], Eq[-1].lhs)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << sets.notcontains.imply.eq.sum.apply(Eq[0], Eq[-1].lhs.find(Sum, Sum))

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[1] * abs(X)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Add[Mul[Abs]]).apply(algebra.add.to.mul)

    Eq << Eq[-1].this.find(Add[Mul[Abs]]).apply(algebra.add.to.mul)


if __name__ == '__main__':
    run()