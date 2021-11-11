from util import *


@apply
def apply(all_historic):    
    (xi, xj), (j, _zero, i_), (i, zero, n) = all_historic.of(All[Unequal])
    if xi._has(j):
        xi, xj = xj, xi

    assert zero == _zero == 0    
    assert i == i_
    assert xi._subs(i, j) == xj
    setc = Cup[i:n]({xi})
    return Equal(Card(setc), n, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    a, i, j= Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
    Eq << apply(All[j:i, i:n](Unequal(x[i], x[j])))

    f = Function(real=True, eval=lambda _: S.One)
    Eq << algebra.all_ne.imply.eq.sum.double_limits.apply(Eq[0], Sum[a:Eq[1].lhs.arg](f(a)))

    Eq << Eq[-1].this.lhs.expr.defun()
    Eq << Eq[-1].this.rhs.expr.defun()


if __name__ == '__main__':
    run()
# created on 2021-01-14
# updated on 2021-01-14
