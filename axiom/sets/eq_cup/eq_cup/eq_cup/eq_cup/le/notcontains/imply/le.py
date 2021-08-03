from util import *


@apply
def apply(*given):
    eqs = []
    for cond in given:
        if cond.is_NotContains:
            notcontains = cond
        elif cond.is_LessEqual:
            le = cond
        else:
            eqs.append(cond)
            
    ((t, y_), (((_t, _x), (x, X)), _X)), ((__t, _y_), (((___t, y), (_y, _Y)), Y))= le.of(Abs[Indexed - Sum[Indexed] / Abs] <= Abs[Indexed - Sum[Indexed] / Abs])            
    assert t == _t == __t == ___t
    assert X == _X and x == _x
    assert y_ ==  _y_
    assert Y == _Y and y == _y
    
    eq_cup_X, eq_cup_Y, eq_cup_X_union, eq_cup_Y_complement = eqs

    _y_, X = notcontains.of(NotContains)
    assert _y_ == y_
    
    ((a, i), (_i, n)), X = eq_cup_X.of(Equal[Cup[FiniteSet[Indexed], Tuple[0]]])
    assert _i == i
    
    ((a_, i), (_i, n1)), X_union = eq_cup_X_union.of(Equal[Cup[FiniteSet[Indexed], Tuple[0]]])
    assert i == _i
        
    ((b, i), (_i, m)), Y = eq_cup_Y.of(Equal[Cup[FiniteSet[Indexed], Tuple[0]]])
    assert _i == i
    
    ((b_, i), (_i, m1)), Y_complement = eq_cup_Y_complement.of(Equal[Cup[FiniteSet[Indexed], Tuple[0]]])
    assert i == _i
        
    if not X_union.is_Union:
        eq_cup_Y, eq_cup_X_union = eq_cup_X_union, eq_cup_Y
        ((a_, i), (_i, n1)), X_union = eq_cup_X_union.of(Equal[Cup[FiniteSet[Indexed], Tuple[0]]])
        assert i == _i        
        ((b, i), (_i, m)), Y = eq_cup_Y.of(Equal[Cup[FiniteSet[Indexed], Tuple[0]]])
        assert _i == i
        
    assert n1 == n + 1    
    assert m1 == m - 1

    y__, _X = X_union.of(Union[FiniteSet, Basic])
    assert _X == X
    assert y__ == y_
    
    _Y, y__ = Y_complement.of(Complement[Basic, FiniteSet])
    assert _Y == Y
    assert y__ == y_
    
    X_ = X | {y_}
    Y_ = Y - {y_}    
        
    return LessEqual(Sum[x:X_]((t[x] - (Sum[x:X_](t[x])) / (abs(X) + 1)) ** 2) + Sum[y:Y_]((t[y] - Sum[y:Y_](t[y]) / (abs(Y) - 1)) ** 2),
                     Sum[x:X]((t[x] - (Sum[x:X](t[x])) / abs(X)) ** 2) + Sum[y:Y]((t[y] - Sum[y:Y](t[y]) / abs(Y)) ** 2))


@prove
def prove(Eq):
    from axiom import sets, algebra

    y = Symbol(integer=True)
    x = Symbol(integer=True)
    y_ = Symbol("y'", integer=True, given=True)
    t = Symbol(real=True, shape=(oo,), given=True)
    X = Symbol(etype=dtype.integer, finiteset=True, given=True)
    Y = Symbol(etype=dtype.integer, finiteset=True, given=True)
    a = Symbol(shape=(oo,), integer=True)
    b = Symbol(shape=(oo,), integer=True)
    a_ = Symbol("a'", shape=(oo,), integer=True)
    b_ = Symbol("b'", shape=(oo,), integer=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(X, Cup[i:abs(X)]({a[i]})), Equal(Y, Cup[i:abs(Y)]({b[i]})), Equal(X | {y_}, Cup[i:abs(X) + 1]({a_[i]})), Equal(Y - {y_}, Cup[i:abs(Y) - 1]({b_[i]})), abs(t[y_] - Sum[x:X](t[x]) / abs(X)) <= abs(t[y_] - Sum[y:Y](t[y]) / abs(Y)), NotContains(y_, X))

    Eq << sets.eq_cup.imply.eq.sum.apply(Eq[0], Eq[6].rhs.args[0].find(Pow, Sum))

    Eq.given = Eq[4].subs(Eq[-1])

    Eq << sets.eq_cup.imply.eq.sum.apply(Eq[0], Eq[6].rhs.args[0])

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq << sets.eq_cup.imply.eq.sum.apply(Eq[1], Eq[6].rhs.args[1].find(Pow, Sum))

    Eq.given = Eq.given.subs(Eq[-1])

    Eq << sets.eq_cup.imply.eq.sum.apply(Eq[1], Eq[6].rhs.args[1])

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq.add_ab = Eq[-4] + Eq[-1]

    Eq.abs_union = sets.notcontains.imply.eq.abs.apply(Eq[5])

    Eq << Eq[2].subs(Eq.abs_union.reversed)

    Eq << sets.eq_cup.imply.eq.sum.apply(Eq[-1], Eq[6].lhs.args[0].find(Pow, Sum))

    Eq << sets.eq_cup.imply.eq.sum.apply(Eq[-2], Eq[6].lhs.args[0])

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq.eq_X_union = Eq[-1].subs(Eq.abs_union)

    Eq.contains = sets.eq_cup.imply.contains.apply(Eq[3])

    Eq.abs_complement = sets.contains.imply.eq.abs.complement.apply(Eq.contains)

    Eq << Eq[3].subs(Eq.abs_complement.reversed)

    Eq << sets.eq_cup.imply.eq.sum.apply(Eq[-1], Eq[6].lhs.args[1].find(Pow, Sum))

    Eq << sets.eq_cup.imply.eq.sum.apply(Eq[-2], Eq[6].lhs.args[1])

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq.eq_Y_complement = Eq[-1].subs(Eq.abs_complement)

    Eq << sets.eq_cup.contains.imply.any.eq.apply(Eq[1], Eq.contains)

    Eq << algebra.cond.any.imply.any_et.apply(Eq.given, Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.et.imply.et.invoke, algebra.eq.cond.imply.cond.subs)

    Eq << algebra.any.imply.any_et.limits.cond.apply(Eq[-1], 0, simplify=None)

    Eq << algebra.any_et.imply.any.limits_absorb.apply(Eq[-1], 1, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.et.imply.et.invoke, sets.le_abs.contains.imply.le, simplify=None)

    Eq << Eq[-1].subs(Eq.add_ab.reversed)

    Eq << Eq[-1].this.expr.args[1].apply(algebra.cond.imply.et.invoke, sets.contains.imply.eq.sum, Eq[-1].expr.args[0].lhs.args[3].find(Sum), simplify=None)

    Eq << Eq[-1].this.expr.args[::2].apply(algebra.eq.cond.imply.cond.subs, simplify=None)

    Eq << Eq[-1].this.expr.args[1].apply(sets.contains.imply.eq.sum, Eq[-1].expr.args[0].lhs.args[3])

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, simplify=None)

    Eq << algebra.any.imply.any_et.limits.cond.apply(Eq[-1], 0, simplify=None)

    Eq << algebra.any_et.imply.any.limits_absorb.apply(Eq[-1], 1, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True)

    Eq << sets.eq_cup.eq_cup.notcontains.imply.eq.sum.apply(Eq[0], Eq[2], Eq[5], Eq.eq_X_union.rhs.find(Sum))

    Eq << Eq[-2].subs(Eq[-1].reversed)

    j = Eq[-1].expr.lhs.args[1].variable
    Eq << Eq[-1].this.expr.lhs.args[1].limits_subs(j, i, simplify=None)

    Eq << sets.eq_cup.eq_cup.notcontains.imply.eq.sum.apply(Eq[0], Eq[2], Eq[5], Eq.eq_X_union.rhs)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << algebra.cond.any.imply.any_et.apply(Eq[1] & Eq[3], Eq[-1], simplify=None)

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[:4].apply(algebra.et.imply.et.invoke, sets.eq.eq.eq.contains.imply.eq.sum, Eq[-1].expr.args[4].lhs.args[1].find(Sum), simplify=None, ret=None)

    Eq << Eq[-1].this.expr.args[4:6].apply(algebra.eq.cond.imply.cond.subs, simplify=None)

    Eq << Eq[-1].this.expr.args[:4].apply(sets.eq.eq.eq.contains.imply.eq.sum, Eq[-1].expr.args[4].lhs.args[1], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs)

    Eq << Eq[-1].subs(Eq.eq_X_union.reversed, Eq.eq_Y_complement.reversed)


if __name__ == '__main__':
    run()