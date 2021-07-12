from util import *


@apply
def apply(sgm):
    fx, (x, X) = sgm.of(Sum)
    
    (a, i), (_i, n) = X.of(Cup[FiniteSet[Indexed], Tuple[0]])
    assert _i == i
    j = sgm.generate_var(excludes=i, var='j', integer=True)
    
    return Suffice(All[j:i, i:n](Unequal(a[i], a[j])), Equal(sgm, Sum[i:n](fx._subs(x, a[i]))))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=False)
    X = Symbol.X(etype=dtype.real)
    x = Symbol.x(real=True)
    a = Symbol.a(real=True, shape=(oo,))
    f = Function.f(real=True)
    s = a[:n].set_comprehension()
    Eq << apply(Sum[x:s](f(x)))

    Eq.initial = Eq[0].subs(n, 1)

    Eq.induct = Eq[0].subs(n, n + 1)


if __name__ == '__main__':
    run()