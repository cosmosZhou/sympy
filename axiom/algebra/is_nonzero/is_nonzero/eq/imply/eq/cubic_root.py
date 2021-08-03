from util import *


@apply
def apply(is_nonzero_A, is_nonzero_B, eq):
    A = is_nonzero_A.of(Unequal[0])
    B = is_nonzero_B.of(Unequal[0])    
    w = -S.One / 2 + sqrt(3) / 2 * S.ImaginaryUnit
    eq.lhs.of(Ceiling[Expr - Expr])
    (((A, B), pi2), half), d = eq.of(Equal[Ceiling[(Arg + Arg) * Expr - Expr]])
    assert 1 / pi2 == S.Pi * 2 and half * 2 == 1
    
    if d == 0:    
        factor = 1        
    elif d % 3 == 1:
        factor = w
    else:
        factor = ~w
    
    
    return Equal(A ** (S.One / 3) * B ** (S.One / 3), (A * B) ** (S.One / 3) * factor)


@prove
def prove(Eq):
    from axiom import algebra

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Unequal(A, 0), Unequal(B, 0), Equal(Ceiling((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2), 1))

    Eq << Eq[-1].this.lhs.args[0].base.apply(algebra.expr.to.mul.expi)

    Eq << Eq[-1].this.lhs.args[0].base.apply(algebra.expr.to.mul.expi)

    Eq << Eq[-1].this.find(Pow[~Mul]).apply(algebra.expr.to.mul.expi)

    Eq << Eq[-1].this.find(Abs[Mul]).apply(algebra.abs.to.mul)

    Eq << algebra.eq.given.eq.div.apply(Eq[-1], Mul(*Eq[-1].lhs.args[:2]))

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.root.to.mul.expi.arg)

    Eq << Eq[-1].this.lhs.args[0].apply(algebra.root.to.mul.expi.arg)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.root.to.mul.expi.arg)

    Eq << Eq[-1].rhs.find(Arg).this.apply(algebra.arg_mul.to.piecewise)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0] & Eq[1], Eq[-1], invert=True)

    Eq << Eq[-1].subs(Eq[2])

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.args[1].arg.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.exp.to.mul)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.expr.to.add.complex)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add, deep=True)

    


if __name__ == '__main__':
    run()