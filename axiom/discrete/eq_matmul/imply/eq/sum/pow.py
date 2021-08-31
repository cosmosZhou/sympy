from util import *


@apply
def apply(given, m, i=None):
    (x, w), y = given.of(Equal[MatMul])
    [n] = x.shape
    _n, _i, _j = w.of(Swap)
    assert n == _n
    assert _i >= 0 and _i < n
    assert _j >= 0 and _j < n
    if i is None:
        i = given.generate_var(integer=True, var='i')

    return Equal(Sum[i:n](x[i] ** m), Sum[i:n](y[i] ** m))


@prove(proved=False)
def prove(Eq):
    from axiom import discrete

    m = Symbol(integer=True, positive=True, given=False)
    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True, given=True)
    i, j = Symbol(domain=Range(0, n))
    Eq << apply(Equal(x @ Swap(n, i, j), y), m)

    Eq.initial = Eq[1].subs(m, 1)

    _i = Eq[1].lhs.variable
    Eq << discrete.eq_matmul.imply.eq.sum.apply(Eq[0], _i)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.simplify()

    Eq.induct = Eq[1].subs(m, m + 1)



if __name__ == '__main__':
    run()
