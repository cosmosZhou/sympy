from util import *


@apply
def apply(eq_cup):
    ((b, k), (_k, n)), X_complement = eq_cup.of(Equal[Cup[FiniteSet[Indexed], Tuple[0]]])
    assert k == _k
    n += 1
    X = n.of(Abs)
    
    _X, y = X_complement.of(Complement[Basic, FiniteSet])
    assert _X == X
    
    return Contains(y, X)


@prove
def prove(Eq):
    from axiom import sets, algebra

    X = Symbol.X(etype=dtype.real, given=True)
    x = Symbol.x(real=True)
    y = Symbol.y(real=True, given=True)
    b = Symbol.b(real=True, shape=(oo,))
    f = Function.f(real=True)
    n = Abs(X)
    Eq << apply(Equal(X - {y}, b[:n - 1].set_comprehension()))

    Eq << ~Eq[1]

    Eq << sets.notcontains.imply.eq.complement.apply(Eq[-1])

    Eq << Eq[0].subs(Eq[-1])

    Eq << sets.imply.le.cup.apply(*Eq[-1].rhs.args)

    Eq << algebra.eq.imply.eq.abs.apply(Eq[-2])
    Eq << algebra.eq.le.imply.le.subs.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()