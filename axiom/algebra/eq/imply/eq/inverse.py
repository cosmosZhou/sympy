from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    assert lhs.is_nonzero or rhs.is_nonzero
    return Equal(1 / lhs, 1 / rhs)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n,))
    a = Symbol.a(real=True)
    b = Symbol.b(real=True, shape=(n,), zero=False)
    Eq << apply(Equal(x * a, b))

    Eq << Eq[-1].subs(Eq[0])

    


if __name__ == '__main__':
    run()
