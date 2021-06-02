from util import *


import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    p, q = self.of(Add)
    p = p.of(Bool)
    q = q.of(Bool)

    return Equal(self, Bool(p | q) + Bool(p & q))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)

    Eq << apply(Bool(Contains(x, A)) + Bool(Contains(x, B)))

    Eq << Eq[-1].this.rhs.args[1].arg.apply(sets.contains.to.ou.split.union)

    Eq << Eq[-1].this.find(Bool[Or]).apply(algebra.bool.to.add)


if __name__ == '__main__':
    run()

