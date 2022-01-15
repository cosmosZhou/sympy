from util import *


@apply
def apply(self):
    function, (x, space) = self.of(Sum)
    x, *indices = x.of(Sliced)

    assert len(indices) == 1
    domain, *shape = space.of(CartesianSpace)
    assert len(shape) == 1
    n = shape[0]

    start, stop = indices[0]
    assert start + 1 < stop
    assert n == stop - start

    return Equal(self, Sum[x[start]:domain, x[start + 1:stop]:CartesianSpace(domain, n - 1)](function))


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n - 1))
    x = Symbol(integer=True, shape=(oo,))
    f = Function(real=True, shape=())
    Eq << apply(Sum[x[i:n]:CartesianSpace(Range(a, b + 1), n - i)](f(x[i:n])))

    Eq << Eq[0].this.lhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.find(Element).simplify()

    Eq << Eq[-1].this.rhs.find(All).apply(algebra.all.limits.subs.offset, -i - 1)

    Eq << Eq[-1].this.rhs.find(And).apply(algebra.et.to.all.limits.push_front)

    Eq << Eq[-1].this.lhs.find(Element).simplify()

    Eq << Eq[-1].this.lhs.find(All).apply(algebra.all.limits.subs.offset, -i)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.split.slice.pop_front)


if __name__ == '__main__':
    run()

from . import baseset
# created on 2020-03-19
