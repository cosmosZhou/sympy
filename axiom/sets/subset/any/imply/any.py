from util import *


@apply
def apply(subset, exist):
    expr, *limits = exist.of(Any)

    B, A = subset.of(Subset)

    index = -1
    for i, (x, *domain) in enumerate(limits):
        if len(domain) == 1:
            if domain[0] == B:
                index = i
                break

    assert index >= 0

    limits[index] = (x, A)
    return Any(expr, *limits)


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(complex=True, positive=True)
    A, B = Symbol(etype=dtype.complex * n)
    x = Symbol(complex=True, shape=(n,))
    f = Function(complex=True, shape=())
    Eq << apply(Subset(B, A), Any[x:B](f(x) > 1))

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[1], simplify=None)

    Eq << algebra.cond.any.imply.any_et.apply(Eq[0], Eq[-1], simplify=None)
    Eq << Eq[-1].this.expr.args[::2].apply(sets.el.subset.imply.el)


if __name__ == '__main__':
    run()