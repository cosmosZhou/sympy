from util import *


@apply
def apply(less_than, equal):
    k, n = less_than.of(LessEqual)
    a, b = equal.of(Equal)
    assert a.shape == b.shape
    assert n <= a.shape[0] == b.shape[0]

    return Equal(a[:k], b[:k])

@prove
def prove(Eq):
    k, n = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(n,))
    Eq << apply(LessEqual(k, n), Equal(x, y))

    Eq << Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    run()

# created on 2020-12-30
# updated on 2020-12-30
