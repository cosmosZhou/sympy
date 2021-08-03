from util import *


@apply
def apply(eq_cup, eq_cup_union, notcontains, sgm, *, assumptions=None):
    ((a, i), (_i, n)), X = eq_cup.of(Equal[Cup[FiniteSet[Indexed], Tuple[0]]])
    assert _i == i
    ((b, __i), (___i, n1)), X_union = eq_cup_union.of(Equal[Cup[FiniteSet[Indexed], Tuple[0]]])
    assert i == _i == __i == ___i
    assert n1 == n + 1

    y, _X = X_union.of(Union[FiniteSet, Basic])
    assert _X == X
    fbi, (i, n1) = sgm.of(Sum[Tuple[0]])    
    assert n1 == n + 1

    _X = n.of(Abs)
    assert _X == X
    
    _y, _X = notcontains.of(NotContains)
    assert _X == X
    assert _y == y
    
    if assumptions is None:
        assumptions = {}
    if i not in assumptions:
        assumptions[i] = False
        
    return Equal(sgm, Sum[i:n](fbi._subs(b[i], a[i], assumptions=assumptions)) + fbi._subs(b[i], y, assumptions=assumptions))


@prove
def prove(Eq):
    from axiom import sets, algebra

    i = Symbol.i(integer=True)
    X = Symbol.X(etype=dtype.real)
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True, shape=(oo,))
    b = Symbol.b(real=True, shape=(oo,))
    f = Function.f(real=True)
    n = Abs(X)
    Eq << apply(Equal(X, a[:n].set_comprehension()), Equal(X | {y}, b[:n + 1].set_comprehension()), NotContains(y, X), Sum[i:n + 1](f(b[i])))

    Eq << sets.eq_cup.imply.eq.sum.apply(Eq[0], Sum[x:X](f(x)))

    Eq.plausible = Eq[3].subs(Eq[-1].reversed)

    Eq << sets.notcontains.imply.eq.abs.apply(Eq[2])

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << sets.eq_cup.imply.eq.sum.apply(Eq[-1], Sum[x:X | {y}](f(x)))

    Eq << Eq[-1].subs(Eq[-3])

    Eq << Eq.plausible.subs(Eq[-1].reversed)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.split, cond={y})

    Eq << sets.notcontains.imply.eq.complement.apply(Eq[2])

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()