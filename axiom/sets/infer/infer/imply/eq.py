from util import *


@apply
def apply(sufficient_A, sufficient_B):
    x_in_A, x_in_B = sufficient_A.of(Infer)

    S[x_in_B], S[x_in_A] = sufficient_B.of(Infer)

    x, A = x_in_A.of(Element)
    S[x], B = x_in_B.of(Element)

    return Equal(A, B)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    A, B = Symbol(etype=dtype.integer * n)

    Eq << apply(Infer(Element(x, A), Element(x, B)), Infer(Element(x, B), Element(x, A)))

    Eq << sets.infer.assuming.imply.eq.apply(Eq[0], Eq[1].reversed)


if __name__ == '__main__':
    run()

# created on 2018-09-20
