from util import *


import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    b = self.of(Bool)
    p, q = b.of(Or)

    return Equal(self, Bool(p) + Bool(q) - Bool(p & q))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    Eq << apply(Bool(Or(Contains(x, A), Contains(x, B))))

    Eq << Eq[0].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Add(*Eq[-1].rhs.args[:2]).this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.rhs.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.piecewise.st.two_pieces)

    Eq << Bool(Contains(x, A & B)).this.apply(algebra.bool.to.piecewise)

    Eq << Eq[-2] - Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.piecewise.st.two_pieces)

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[-1].this.find(Or).simplify()

if __name__ == '__main__':
    run()

