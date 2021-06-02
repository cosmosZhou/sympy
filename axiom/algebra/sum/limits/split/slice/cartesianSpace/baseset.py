from util import *


@apply
def apply(self):
    import axiom
    function, *limits = self.of(Sum)
    x, cond, space = axiom.limit_is_baseset(limits)
    x, *indices = x.of(Slice)

    assert len(indices) == 1
    domain, *shape = space.of(CartesianSpace)
    assert len(shape) == 1
    n = shape[0]

    start, stop = indices[0]
    assert start + 1 < stop
    assert n == stop - start

    return Equal(self, Sum[x[start]:cond:domain, x[start + 1:stop]:CartesianSpace(domain, n - 1)](function))


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Range(0, n - 1))
    x = Symbol.x(integer=True, shape=(oo,))
    f = Function.f(real=True, shape=())
    g = Function.g(real=True, shape=())
    Eq << apply(Sum[x[i:n]:g(x[i:n]) > 0:CartesianSpace(Range(a, b + 1), n - i)](f(x[i:n])))

    Eq << Eq[0].this.lhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.find(Contains).simplify()

    j = Eq[-1].find(ForAll).variable
    Eq << Eq[-1].this.rhs.find(ForAll).limits_subs(j, j - i - 1)

    Eq << Eq[-1].this.lhs.find(Contains).simplify()

    Eq << Eq[-1].this.lhs.find(ForAll).limits_subs(j, j - i)

    Eq << Eq[-1].this.lhs.find(ForAll).apply(algebra.all.to.et.dissect, cond={i})

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.split.slice)


if __name__ == '__main__':
    run()

