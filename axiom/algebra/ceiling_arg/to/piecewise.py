from util import *


@apply
def apply(self):
    ((AB, pi2), half) = self.of(Ceiling[Arg * Expr - Expr])
    assert pi2 == 3 / (S.Pi * 2)
    assert half * 2 == 1

    delta_0, delta_1 = AB.of(Expr ** (S.One / 3) * Expr ** (S.One / 3))

    q = (delta_0 + delta_1) / -2

    delta = (delta_1 - delta_0) / 2
    delta **= 2
    
    p3 = (delta - q ** 2) * 27 / 4    
    p = p3.of(Expr ** 3)
    U = sqrt(delta) - q
    V = -sqrt(delta) - q

    return Equal(self, Piecewise((0, Equal(p * Ceiling((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True)))


@prove
def prove(Eq):
    from axiom import algebra

    p, q = Symbol(complex=True, given=True)
    delta = 4 * p ** 3 / 27 + q ** 2
    U = sqrt(delta) - q
    V = -sqrt(delta) - q
    Eq << apply(Ceiling(3 * Arg(U ** (S.One / 3) * V ** (S.One / 3)) / (S.Pi * 2) - S.One / 2))

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[0], cond=Equal(p, 0))

    Eq << algebra.suffice.given.suffice.subs.apply(Eq[-2])

    Eq << algebra.mul_root.to.mul_piecewise.cubic_root.apply(Eq[-1].find(Arg[~Mul]))

    Eq << Eq[-1].this.find(Pow[~Mul]).apply(algebra.mul.to.add, deep=True)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Unequal(p, 0).this.apply(algebra.is_nonzero.imply.eq.ceiling_arg.to.piecewise, q)

    Eq << Eq[-1].lhs.this.apply(algebra.is_nonzero.imply.equivalent.eq, Eq[-1].find(Equal[~Ceiling, 0]))

    Eq <<= Eq[-1] & Eq[-2]
    Eq << Eq[-1].this.rhs.apply(algebra.equivalent.cond.imply.cond.subs)
    


if __name__ == '__main__':
    run()