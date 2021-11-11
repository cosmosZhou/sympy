from util import *


@apply
def apply(x, y):
    assert x.shape == y.shape
    assert len(x.shape) == 1
    return Equal(x @ y, y @ x)


@prove
def prove(Eq):
    from axiom import discrete
    n = Symbol(integer=True)
    x, y = Symbol(shape=(n,), real=True)
    i = Symbol(domain=Range(n))
    Eq << apply(x, y)

    Eq << Eq[0].lhs.this.apply(discrete.matmul.to.sum, var=i)

    Eq << Eq[0].rhs.this.apply(discrete.matmul.to.sum, var=i)

    Eq << Eq[-2].subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()
# created on 2020-08-16
# updated on 2020-08-16
