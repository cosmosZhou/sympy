from util import *


@apply
def apply(eq, sgm):
    (ai, (i, n)), X = eq.of(Equal[Cup[FiniteSet, Tuple[0]]])
    _X = n.of(Abs)
    assert X == _X
    
    fx, (x, __X) = sgm.of(Sum)
    assert X == _X == __X
    
    return Equal(sgm, Sum[i:n](fx._subs(x, ai)))


@prove
def prove(Eq):
    from axiom import sets

    X = Symbol.X(etype=dtype.real, emptyset=False)
    x = Symbol.x(real=True)
    a = Symbol.a(real=True, shape=(oo,))
    f = Function.f(real=True)
    Eq << apply(Equal(X, a[:abs(X)].set_comprehension()), Sum[x:X](f(x)))

    n = Symbol.n(abs(X))
    Eq << n.this.definition.reversed

    Eq << Eq[0].subs(Eq[-1])

    Eq << sets.eq.eq.imply.eq.sum.apply(Eq[-1], Eq[-2], Eq[1].lhs)

    Eq << Eq[1].subs(Eq[2])


if __name__ == '__main__':
    run()