from util import *


@apply
def apply(is_nonzero, equality):
    lhs = is_nonzero.of(Unequal[0])
    _lhs, rhs = equality.of(Equal)
    assert lhs == _lhs

    return Equal(log(lhs), log(rhs))


@prove
def prove(Eq):
    x = Symbol(real=True)
    f, g = Function(shape=(), real=True)

    Eq << apply(Unequal(f(x), 0), Equal(f(x), g(x)))

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1].subs(Eq[1].reversed)


if __name__ == '__main__':
    run()

# created on 2021-08-02
# updated on 2021-08-02