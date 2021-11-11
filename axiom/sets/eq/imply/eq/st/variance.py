from util import *


@apply
def apply(eq):
    (a, y), (((_a, _x), (x, X)), _X) = eq.of(Equal[Indexed, Sum[Indexed] / Card])

    assert a == _a
    assert X == _X and x == _x

    X_ = X | {y}
    return Equal(Sum[x:X_]((a[x] - (Sum[x:X_](a[x])) / (Card(X_))) ** 2),
                 Sum[x:X]((a[x] - (Sum[x:X](a[x])) / Card(X)) ** 2))


@prove
def prove(Eq):
    from axiom import algebra, sets

    y = Symbol(integer=True, given=True)
    x = Symbol(integer=True)
    a = Symbol(real=True, shape=(oo,), given=True)
    X = Symbol(etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(Equal(a[y], Sum[x:X](a[x]) / Card(X)))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[1], cond=Element(y, X))

    Eq << Element(y, X).this.apply(sets.el.imply.eq.union)

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.eq)

    Eq << algebra.cond.imply.infer.apply(Eq[0], cond=Eq[3].lhs)

    Eq << algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(sets.eq.notin.imply.eq.st.variance)


if __name__ == '__main__':
    run()
# created on 2021-04-03
# updated on 2021-04-03
