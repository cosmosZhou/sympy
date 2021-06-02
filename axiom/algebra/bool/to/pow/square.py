from util import *

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    assert self.is_Bool
    return Equal(self, self * self)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(Bool(x > y))

    b = Symbol.b(Eq[0].lhs)
    Eq << Or(Equal(b, 0), Equal(b, 1), plausible=True)

    Eq << Eq[-1].this.args[0].lhs.definition

    Eq << Eq[-1].this.args[0].lhs.definition

    Eq << sets.imply.contains.bool.apply(Eq[0].lhs)

    Eq << sets.contains.imply.ou.split.finiteset.two.apply(Eq[-1])

    Eq << algebra.ou.imply.is_zero.apply(Eq[1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.base.definition


if __name__ == '__main__':
    run()

