from util import *


@apply
def apply(imply):
    (x, S), *limits = imply.of(Any[Element])
    return Element(x, Cup(S, *limits))


@prove
def prove(Eq):
    from axiom import sets

    n = Symbol(positive=True, integer=True)
    x, k = Symbol(integer=True)
    A = Symbol(shape=(oo,), etype=dtype.integer)
    Eq << apply(Any[k:n](Element(x, A[k])))

    Eq << sets.el.given.any_el.st.cup.apply(Eq[1])


if __name__ == '__main__':
    run()
