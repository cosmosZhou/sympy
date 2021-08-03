from util import *


@apply
def apply(imply):
    (x, S), *limits = imply.of(Any[Contains])
    return Contains(x, Cup(S, *limits))


@prove
def prove(Eq):
    from axiom import sets

    n = Symbol.n(positive=True, integer=True)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)
    A = Symbol.A(shape=(oo,), etype=dtype.integer)
    Eq << apply(Any[k:n](Contains(x, A[k])))

    Eq << sets.contains.given.any_contains.st.cup.apply(Eq[1])


if __name__ == '__main__':
    run()