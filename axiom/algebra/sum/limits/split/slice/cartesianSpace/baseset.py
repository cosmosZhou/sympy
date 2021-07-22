from util import *


@apply
def apply(self):
    function, ((x, (start, stop)), cond, (domain, *shape)) = self.of(Sum[Tuple[Slice, CartesianSpace]])

    [n] = shape
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

    j = Eq[-1].find(All).variable
    Eq << Eq[-1].this.rhs.find(All).limits_subs(j, j - i - 1)

    Eq << Eq[-1].this.lhs.find(Contains).simplify()

    Eq << Eq[-1].this.lhs.find(All).limits_subs(j, j - i)

    Eq << Eq[-1].this.lhs.find(All).apply(algebra.all.to.et.split, cond={i})

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.split.slice.pop_front)


if __name__ == '__main__':
    run()

