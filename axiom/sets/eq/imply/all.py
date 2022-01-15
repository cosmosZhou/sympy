from util import *


@apply
def apply(given):
    A, (_x, (x, condition)) = given.of(Equal[Expr, Cup[FiniteSet]])
    assert x == _x
    return All[x:A](condition)


@prove
def prove(Eq):
    x = Symbol(integer=True)
    A = Symbol(etype=dtype.integer)

    f = Function(integer=True)

    Eq << apply(Equal(conditionset(x, f(x) > 0), A))

    Eq << Eq[-1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()

# created on 2020-12-26
