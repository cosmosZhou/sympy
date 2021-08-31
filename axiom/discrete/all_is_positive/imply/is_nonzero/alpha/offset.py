from util import *
from axiom.discrete.imply.is_positive.alpha import alpha


@apply
def apply(given):
    (x, _j), (j, a, n) = given.of(All[Indexed > 0])

    offset = _j - j
    if offset != 0:
        assert not offset._has(j)

    a += offset
    n += offset
    return Unequal(alpha(x[a:n]), 0)


@prove
def prove(Eq):
    from axiom import algebra, discrete

    x = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    a = Symbol(integer=True, nonnegative=True)
    b, i = Symbol(integer=True)
    Eq << apply(All[i:a:n](x[i + b] > 0))

    x_ = Symbol.x(x[a + b:])
    Eq << x_[i].this.definition

    Eq << Eq[0].this.apply(algebra.all.limits.subs.offset, a)

    Eq << Eq[-1].subs(Eq[-2].reversed)

    Eq << discrete.all_is_positive.imply.is_nonzero.alpha.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.arg.definition


if __name__ == '__main__':
    run()
