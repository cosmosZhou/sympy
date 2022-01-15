from util import *


@apply
def apply(self):
    function, ((x, (start, stop)), cond, (domain, *shape)) = self.of(Sum[Tuple[Sliced, CartesianSpace]])

    [n] = shape
    assert start + 1 < stop
    assert n == stop - start

    return Equal(self, Sum[x[start]:cond:domain, x[start + 1:stop]:CartesianSpace(domain, n - 1)](function))


@prove
def prove(Eq):
    from axiom import algebra
    a, b = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(n - 1))
    x = Symbol(integer=True, shape=(oo,))
    f, g = Function(real=True, shape=())
    Eq << apply(Sum[x[i:n]:g(x[i:n]) > 0:CartesianSpace(Range(a, b + 1), n - i)](f(x[i:n])))

    Eq << Eq[0].this.lhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.find(Element).simplify()

    Eq << Eq[-1].this.rhs.find(All).apply(algebra.all.limits.subs.offset, -i - 1)

    Eq << Eq[-1].this.lhs.find(Element).simplify()

    Eq << Eq[-1].this.lhs.find(All).apply(algebra.all.limits.subs.offset, -i)

    Eq << Eq[-1].this.lhs.find(All).apply(algebra.all.to.et.split, cond={i})

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.split.slice.pop_front)


if __name__ == '__main__':
    run()

# created on 2020-03-18
