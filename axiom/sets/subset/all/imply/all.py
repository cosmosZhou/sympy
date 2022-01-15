from util import *


@apply
def apply(subset, forall):
    function, *limits = forall.of(All)

    B, A = subset.of(Subset)

    index = -1
    for i, (x, *domain) in enumerate(limits):
        if len(domain) == 1:
            if domain[0] == A:
                index = i
                break

    assert index >= 0

    limits[index] = (x, B)
    return All(function, *limits)


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(complex=True, positive=True)
    A, B = Symbol(etype=dtype.complex * n)
    x = Symbol(complex=True, shape=(n,))
    f = Function(complex=True, shape=())
    Eq << apply(Subset(B, A), All[x:A](Equal(f(x), 1)))

    Eq << sets.subset.imply.all_el.apply(Eq[0], wrt=x)

    Eq << algebra.all.imply.infer.apply(Eq[-1])

    Eq << algebra.all.imply.infer.apply(Eq[1])

    Eq << algebra.infer.infer.imply.infer.transit.apply(Eq[-1], Eq[-2])

    Eq << algebra.all.given.infer.apply(Eq[2])


if __name__ == '__main__':
    run()

# created on 2020-04-01
