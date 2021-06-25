from util import *


def doit(Sum, self):
    xi, (i, s) = self.of(Sum)
    assert s.is_FiniteSet

    sgm = self.identity(xi)
    while s:
        t, *args = s.args
        sgm = Sum.operator(sgm, xi._subs(i, t))

        s = FiniteSet(*args)
        assert Contains(t, s).is_BooleanFalse

    return sgm


@apply
def apply(self):
    return Equal(self, doit(Sum, self))


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(oo, k))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    f = Function.f(integer=True)

    n = 5
    finiteset = {i for i in range(n)}

    Eq << apply(Sum[i:finiteset](x[i]))

    n -= 1
    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.split, cond={n})


if __name__ == '__main__':
    run()

