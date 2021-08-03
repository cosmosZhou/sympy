from util import *


@apply
def apply(is_nonzero, q):
    p = is_nonzero.of(Unequal[0])

    delta = 4 * p ** 3 / 27 + q ** 2
    
    U = sqrt(delta) - q
    V = -sqrt(delta) - q

    return Equal(Ceiling(3 * Arg(U ** (S.One / 3) * V ** (S.One / 3)) / (S.Pi * 2) - S.One / 2), Piecewise((0, Equal(Ceiling((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True)))


@prove
def prove(Eq):
    from axiom import algebra, geometry, sets

    p, q = Symbol(complex=True, given=True)
    delta = 4 * p ** 3 / 27 + q ** 2
    A = (sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    B = (-sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    Eq << apply(Unequal(p, 0), q)

    U = Symbol(sqrt(delta) - q)
    V = Symbol(-sqrt(delta) - q)
    A = Symbol((sqrt(delta) / 2 - q / 2) ** (S.One / 3))
    B = Symbol((-sqrt(delta) / 2 - q / 2) ** (S.One / 3))
    Eq.U, Eq.V = U.this.definition, V.this.definition

    Eq << Eq.U * Eq.V

    Eq.UV = Eq[-1].this.rhs.apply(algebra.mul.to.add, deep=True)

    Eq << Eq[1].subs(Eq.U.reversed, Eq.V.reversed)

    Eq << Eq[-1].this.find(Arg[~Mul[Pow]]).apply(algebra.mul_root.to.mul_piecewise.cubic_root)

    Eq << Eq[-1].subs(Eq.UV)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(algebra.mul_piecewise.to.piecewise)

    Eq << Eq[-1].this.find(Arg[Piecewise]).apply(algebra.arg_piecewise.to.piecewise)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(algebra.mul_piecewise.to.piecewise)

    Eq << Eq[-1].this.find(Add[Piecewise]).apply(algebra.add.to.piecewise)

    Eq << Eq[-1].this.find(Ceiling[Piecewise]).apply(algebra.ceiling_piecewise.to.piecewise)

    Eq.eq = Eq[-1].this.find(Ceiling[~Mul]).apply(algebra.mul.to.add)

    Eq << Or(*Eq[-1].find(Or).args[:2]).this.apply(algebra.ou.imply.is_zero)

    Eq << Eq[-1].subs(Eq.UV)

    Eq << Eq[-1].this.rhs * (-Integer(27) / 4)

    Eq.suffice = Eq[-1].this.rhs.apply(algebra.pow_is_zero.imply.is_zero)

    Eq << Equal(U * V, 0).this.apply(algebra.mul_is_zero.imply.ou.is_zero)

    Eq << Eq[-1].subs(Eq.UV)

    Eq << Eq[-1].this.lhs * (-Integer(27) / 4)

    Eq << Eq[-1].this.lhs.apply(algebra.pow_is_zero.given.is_zero)

    Eq <<= Eq.suffice & Eq[-1]

    Eq << algebra.cond.given.cond.subs.cond.apply(Eq.eq, given=Eq[-1])

    Eq.eq_simplified = algebra.cond.given.cond.subs.bool.apply(Eq[-1], given=Eq[0], invert=True)

    Eq.p_cubic = Eq.eq_simplified.find(Pow[Mul]).this.apply(algebra.root.to.mul.expi.arg)

    Eq.p_is_positive = algebra.is_nonzero.imply.abs_is_positive.apply(Eq[0])

    Eq << algebra.is_positive.imply.eq.arg.apply(Eq.p_is_positive, Eq.p_cubic.find(Exp))

    Eq << algebra.eq.imply.eq.arg.apply(Eq.p_cubic)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.apply(algebra.arg_expi.to.mul.arg)

    Eq << Eq[-1].this.find(Arg[Mul]).apply(algebra.arg_mul.to.add.st.pow)

    Eq << Eq.eq_simplified.subs(Eq[-1])

    Eq.eq_simplified = Eq[-1].this.find(Ceiling[Add[~Mul[Add]]]).apply(algebra.mul.to.add)

    Eq << Eq.p_cubic * exp(S.ImaginaryUnit * 2 * S.Pi / 3)

    Eq << algebra.is_positive.imply.eq.arg.apply(Eq.p_is_positive, Mul(*Eq[-1].rhs.args[1:]))

    Eq << algebra.eq.imply.eq.arg.apply(Eq[-2])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.arg.apply(algebra.mul.to.exp)

    Eq.arg_p3_w = Eq[-1].this.lhs.find(Exp).apply(geometry.expi.to.add.euler.formula)

    Eq.p3_contains = sets.imply.contains.arg.apply(-p ** 3)

    Eq << sets.contains.imply.contains.add.apply(Eq.p3_contains, S.Pi * 2, simplify=None)

    Eq << sets.contains.imply.contains.div.interval.apply(Eq[-1], 3, simplify=None)

    Eq << sets.contains.imply.eq.arg_expi.apply(Eq[-1])

    Eq << Eq.arg_p3_w.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Arg[Mul]).apply(algebra.arg_mul.to.add.st.pow)

    Eq << Eq.eq_simplified.subs(Eq[-1])

    Eq << Eq[-1].this.find(ExprCondPair[Ceiling[Add[~Mul[Add]]]]).apply(algebra.mul.to.add)

    Eq.eq_simplified = Eq[-1].this.find(Add[~Ceiling]).apply(algebra.ceiling.to.add.half)

    Eq << Eq.p_cubic * exp(-S.ImaginaryUnit * 2 * S.Pi / 3)

    Eq << algebra.is_positive.imply.eq.arg.apply(Eq.p_is_positive, Mul(*Eq[-1].rhs.args[1:]))

    Eq << algebra.eq.imply.eq.arg.apply(Eq[-2])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.arg.apply(algebra.mul.to.exp)

    Eq.arg_p3_w = Eq[-1].this.lhs.find(Exp).apply(geometry.expi.to.add.euler.formula)

    Eq << sets.contains.imply.contains.sub.apply(Eq.p3_contains, S.Pi * 2, simplify=None)

    Eq << sets.contains.imply.contains.div.interval.apply(Eq[-1], 3, simplify=None)

    Eq << sets.contains.imply.eq.arg_expi.apply(Eq[-1])

    Eq << Eq.arg_p3_w.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Arg[Mul]).apply(algebra.arg_mul.to.add.st.pow)

    Eq << Eq.eq_simplified.subs(Eq[-1])

    Eq << Eq[-1].this.find(ExprCondPair[Ceiling[Add[~Mul[Add]]]]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Add[~Ceiling]).apply(algebra.ceiling.to.add.half)


if __name__ == '__main__':
    run()