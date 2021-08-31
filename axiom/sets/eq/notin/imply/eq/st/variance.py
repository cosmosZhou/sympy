from util import *


@apply
def apply(notcontains, eq):
    if notcontains.is_Equal:
        notcontains, eq = eq, notcontains
    _y, __X = notcontains.of(NotElement)
    (a, y), (((_a, _x), (x, X)), _X) = eq.of(Equal[Indexed, Sum[Indexed] / Card])

    assert a == _a
    assert y == _y
    assert X == _X  == __X and x == _x

    X_ = X | {y}
    return Equal(Sum[x:X_]((a[x] - (Sum[x:X_](a[x])) / (Card(X_))) ** 2),
                 Sum[x:X]((a[x] - (Sum[x:X](a[x])) / Card(X)) ** 2))


@prove
def prove(Eq):
    from axiom import sets, algebra

    y = Symbol(integer=True, given=True)
    x = Symbol(integer=True)
    a = Symbol(real=True, shape=(oo,), given=True)
    X = Symbol(etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(NotElement(y, X), Equal(a[y], Sum[x:X](a[x]) / Card(X)))

    Eq << sets.notin.imply.eq.card.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << sets.notin.imply.eq.sum.apply(Eq[0], Eq[-1].lhs)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << sets.notin.imply.eq.sum.apply(Eq[0], Eq[-1].lhs.find(Sum, Sum))

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[1] * Card(X)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Add[Mul[Card]]).apply(algebra.add.to.mul)

    Eq << Eq[-1].this.find(Add[Mul[Card]]).apply(algebra.add.to.mul)


if __name__ == '__main__':
    run()