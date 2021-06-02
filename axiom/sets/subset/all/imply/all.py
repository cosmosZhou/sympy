
from util import *



@apply
def apply(*given):
    subset, forall = given
    if subset.is_ForAll:
        forall, subset = subset, forall
    assert subset.is_Subset and forall.is_ForAll
    B, A = subset.args

    index = -1
    for i, (x, *domain) in enumerate(forall.limits):
        if len(domain) == 1:
            if domain[0] == A:
                index = i
                break

    assert index >= 0

    function = forall.function
    limits = [*forall.limits]
    limits[index] = (x, B)
    return ForAll(function, *limits)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(complex=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n)
    x = Symbol.x(complex=True, shape=(n,))

    f = Function.f(nargs=(n,), complex=True, shape=())

    assert f.is_complex
    assert f.shape == ()

    Eq << apply(Subset(B, A), ForAll[x:A](Equal(f(x), 1)))

    Eq << sets.subset.imply.all_contains.apply(Eq[0], wrt=x)

    Eq << algebra.all.imply.suffice.apply(Eq[-1])

    Eq << algebra.all.imply.suffice.apply(Eq[1])

    Eq << algebra.suffice.suffice.imply.suffice.transit.apply(Eq[-1], Eq[-2])

    Eq << algebra.all.given.suffice.apply(Eq[2])


if __name__ == '__main__':
    run()

