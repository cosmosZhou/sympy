from util import *


@apply
def apply(le, ge, contains, notcontains):
    ((a, _y_), (((_a, _x), (x, X)), _X)), ((__a, __y_), (((___a, y), (_y, _Y)), __Y))= le.of(Abs[Indexed - Sum[Indexed] / Card] <= Abs[Indexed - Sum[Indexed] / Card])
    ___Y = ge.of(Card >= 2)
    y_, Y = contains.of(Element)
    ___y_, __X = notcontains.of(NotElement)

    assert a == _a == __a == ___a
    assert X == _X == __X and x == _x
    assert y_ == _y_ == __y_ == ___y_
    assert Y == _Y == __Y == ___Y and y == _y

    X_ = X | {y_}
    Y_ = Y - {y_}
    return LessEqual(Sum[x:X_]((a[x] - (Sum[x:X_](a[x])) / (Card(X) + 1)) ** 2) + Sum[y:Y_]((a[y] - Sum[y:Y_](a[y]) / (Card(Y) - 1)) ** 2),
                     Sum[x:X]((a[x] - (Sum[x:X](a[x])) / Card(X)) ** 2) + Sum[y:Y]((a[y] - Sum[y:Y](a[y]) / Card(Y)) ** 2))


@prove
def prove(Eq):
    from axiom import sets, algebra

    y_quote = Symbol(integer=True, given=True)
    x, y = Symbol(integer=True)
    t = Symbol(real=True, shape=(oo,), given=True)
    X, Y = Symbol(etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(abs(t[y_quote] - Sum[x:X](t[x]) / Card(X)) <= abs(t[y_quote] - Sum[y:Y](t[y]) / Card(Y)), Card(Y) >= 2, Element(y_quote, Y), NotElement(y_quote, X))

    a, b, a_quote, b_quote = Symbol(shape=(oo,), integer=True)
    Eq << sets.ge_card.imply.any_eq.apply(Eq[1], b)

    Eq << algebra.le.imply.ne_zero.domain_definition.st.abs.apply(Eq[0])

    Eq << sets.card_ne_zero.imply.any_eq.apply(Eq[-1], a)

    Eq.any_et = algebra.any.any.imply.any_et.apply(Eq[-1], Eq[-3], simplify=None)

    Eq.abs_complement = sets.el.imply.eq.card.complement.apply(Eq[2])

    Eq << algebra.eq.ge.imply.ge.subs.apply(Eq.abs_complement, Eq[1])

    Eq << sets.ge_card.imply.any_eq.apply(Eq[-1], b_quote)

    Eq << Eq[-1].subs(Eq.abs_complement)

    Eq.abs_union = sets.notin.imply.eq.card.apply(Eq[3])

    Eq << algebra.eq.imply.gt_zero.apply(Eq.abs_union)

    Eq << sets.card_gt_zero.imply.any_eq.apply(Eq[-1], a_quote)

    Eq << Eq[-1].subs(Eq.abs_union)

    Eq << algebra.any.any.imply.any_et.apply(Eq[-1], Eq[-4], simplify=None)

    Eq << algebra.any.any.imply.any_et.apply(Eq.any_et, Eq[-1], simplify=None)

    Eq << algebra.cond.any.imply.any_et.apply(Eq[0] & Eq[3], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(sets.eq_cup.eq_cup.eq_cup.eq_cup.le.notin.imply.le)


if __name__ == '__main__':
    run()
# created on 2021-03-25
# updated on 2021-03-25
