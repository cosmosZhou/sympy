from util import *



@apply
def apply(eq, f_eq):
    lhs, rhs = eq.of(Equal)

    args = lhs.of(Mul)
    args = [arg for arg in args if not arg.is_OneMatrix]
    lhs_without_ones = lhs.func(*args)

    assert f_eq._subs(lhs_without_ones, lhs) == f_eq

    return f_eq._subs(lhs_without_ones, rhs)


@prove
def prove(Eq):
    from axiom import algebra
    m, n = Symbol(integer=True, positive=True)

    a = Symbol(real=True, shape=(n,))
    b, c = Symbol(real=True, shape=(m, n))

    S = Symbol(etype=dtype.real * (m, n))
    Eq << apply(Equal(a * OneMatrix(m, n), c), Element(a * b, S))

    a = Symbol(a * OneMatrix(m, n))

    Eq << a.this.definition

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[0], Eq[-1])

    Eq << Eq[-2] * b

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Eq[-1].subs(Eq[-3].reversed)


if __name__ == '__main__':
    run()
# created on 2019-03-22
# updated on 2019-03-22
