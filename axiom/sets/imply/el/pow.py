from util import *

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    b, e = self.of(Pow)
    assert b == -1
    assert e.is_integer
    return Element(self, {-1, 1})


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol(integer=True)

    Eq << apply((-1) ** n)

    p = Symbol((-1) ** n)
    Eq << Equal(abs(p), 1, plausible=True)

    Eq << Eq[-1].this.lhs.arg.definition

    Eq << algebra.eq_abs.imply.ou.apply(Eq[-1])

    Eq << sets.ou_eq.imply.el.finiteset.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.definition


if __name__ == '__main__':
    run()

# created on 2020-03-01
