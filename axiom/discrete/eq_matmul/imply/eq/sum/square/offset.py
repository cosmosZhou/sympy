from util import *


@apply
def apply(given, a, i=None):
    (x, w), y = given.of(Equal[MatMul])
    [n] = x.shape
    _i, _j = w.of(SwapMatrix)    
    assert _i >= 0 and _i < n
    assert _j >= 0 and _j < n
    if i is None:
        i = given.generate_var(integer=True, var='i')

    return Equal(Sum[i:n]((x[i] - a)**2), Sum[i:n]((y[i] - a)**2))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True, given=True)
    a = Symbol(real=True, given=True)
    i, j = Symbol(domain=Range(n))
    Eq << apply(Equal(x @ SwapMatrix(n, i, j), y), a)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.square.to.add)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.square.to.add)

    k = Eq[-1].lhs.variable
    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << discrete.eq_matmul.imply.eq.sum.square.apply(Eq[0], k)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq[-4].subs(Eq[-1])

    Eq << -Eq[-1].this.apply(algebra.eq.simplify.terms.common) / 2

    Eq << discrete.eq_matmul.imply.eq.sum.apply(Eq[0], i)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq[-4].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-11-14
