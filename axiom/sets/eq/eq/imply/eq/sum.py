from util import *


@apply
def apply(eq, eq_abs, sgm):
    ((a, i), (_i, n)), X = eq.of(Equal[Cup[FiniteSet[Indexed], Tuple[0]]])
    assert _i == i

    _X, _n = eq_abs.of(Equal[Abs])    
    fx, (x, __X) = sgm.of(Sum)
    assert X == _X == __X
    
    return Equal(sgm, Sum[i:n](fx._subs(x, a[i])))


@prove
def prove(Eq):
    from axiom import sets

    n = Symbol.n(integer=True, positive=True)
    X = Symbol.X(etype=dtype.real)
    x = Symbol.x(real=True)
    a = Symbol.a(real=True, shape=(oo,))
    f = Function.f(real=True)
    Eq << apply(Equal(X, a[:n].set_comprehension()), Equal(abs(X), n), Sum[x:X](f(x)))

    Eq << Eq[1].subs(Eq[0])

    fx, (x, X) = Eq[2].lhs.of(Sum)
    Eq << sets.eq.imply.eq.sum.apply(Eq[-1], Sum[x:Eq[-1].lhs.arg](fx))
    Eq << Eq[-1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()