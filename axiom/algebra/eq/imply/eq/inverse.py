from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    assert lhs.is_nonzero or rhs.is_nonzero
    return Equal(1 / lhs, 1 / rhs)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    a = Symbol(real=True)
    b = Symbol(real=True, shape=(n,), zero=False)
    Eq << apply(Equal(x * a, b))

    Eq << Eq[-1].subs(Eq[0])




if __name__ == '__main__':
    run()
# created on 2021-08-16
# updated on 2021-08-16
