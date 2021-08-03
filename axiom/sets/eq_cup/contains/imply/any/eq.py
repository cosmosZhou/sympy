from util import *


@apply
def apply(eq, contains):
    (ai, (i, n)), X = eq.of(Equal[Cup[FiniteSet, Tuple[0]]])
    _X = n.of(Abs)
    assert X == _X
    
    x, __X = contains.of(Contains)
    assert X == _X == __X
    
    return Any[i:n](Equal(x, ai))


@prove
def prove(Eq):
    from axiom import sets

    X = Symbol.X(etype=dtype.real, emptyset=False)
    x = Symbol.x(real=True)
    a = Symbol.a(real=True, shape=(oo,))
    f = Function.f(real=True)
    Eq << apply(Equal(X, a[:abs(X)].set_comprehension()), Contains(x, X))

    Eq << Eq[1].subs(Eq[0])
    Eq << sets.contains.imply.any_contains.st.cup.apply(Eq[-1])


if __name__ == '__main__':
    run()