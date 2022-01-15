from util import *


def doit(Sum, self):
    xi, (i, s), *limits = self.of(Sum)
    assert s.is_FiniteSet

    sgm = self.identity(xi)
    while s:
        t, *args = s.args
        sgm = Sum.operator(sgm, xi._subs(i, t))

        s = FiniteSet(*args)
        assert Element(t, s).is_BooleanFalse

    assert limits
    return Sum(sgm, *limits)


@apply
def apply(self):
    return Equal(self, doit(Sum, self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    Eq << apply(Sum[j:{0, 1, 2, 3}, i:m](x[i, j]))

    s = Symbol(Lamda[i](Sum[j:{0, 1, 2, 3}](x[i, j])))

    Eq << s[i].this.definition

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(algebra.sum.to.add.doit.setlimit)

    Eq << Eq[-2].subs(Eq[-1]).reversed


if __name__ == '__main__':
    run()

# created on 2020-03-13
