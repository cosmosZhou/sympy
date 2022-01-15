from util import *


def doit(All, self):
    xi, (i, s) = self.of(All)
    assert s.is_FiniteSet

    sgm = self.identity(xi)
    for t in s.args:
        sgm = All.operator(sgm, xi._subs(i, t))

    return sgm


@apply(given=None)
def apply(self):
    return Equivalent(self, doit(All, self), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, shape=(oo,))
    i, a, b, c, d = Symbol(integer=True)


    Eq << apply(All[i:{a, b, c, d}](x[i] > 0))

    Eq << Equivalent(All[i:{a}](x[i] > 0), x[a] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Equivalent(All[i:{b}](x[i] > 0), x[b] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << algebra.iff.iff.imply.iff.et.apply(Eq[-2], Eq[-1])

    Eq << Equivalent(All[i:{c}](x[i] > 0), x[c] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << algebra.iff.iff.imply.iff.et.apply(Eq[-2], Eq[-1])

    Eq << Equivalent(All[i:{d}](x[i] > 0), x[d] > 0, plausible=True)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << algebra.iff.iff.imply.iff.et.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-03-29
