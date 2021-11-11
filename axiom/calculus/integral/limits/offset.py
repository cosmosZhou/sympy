from util import *


@apply
def apply(self, offset):
    expr, (x, *ab) = self.of(Integral)
    if ab:
        a, b = ab
        limit = (x, a - offset, b - offset)
    else:
        limit = (x,)

    return Equal(self, Integral(expr._subs(x, x + offset), limit))


@prove
def prove(Eq):
    from axiom import algebra, calculus

    x, y, a, b, c, d = Symbol(real=True)
    f, g = Function(real=True, integrable=True)
    Eq << apply(Integral[x:a:b](f(x)), d)

    fp = Function("f^+", eval=lambda x : (abs(f(x)) + f(x)) / 2)
    fn = Function("f^-", eval=lambda x : (abs(f(x)) - f(x)) / 2)
    Eq << fp(x).this.defun()

    Eq << algebra.imply.add_ge_zero.abs.apply(f(x)) / 2

    Eq.fp_is_nonnegative = Eq[-1].subs(Eq[-2].reversed)

    Eq << fn(x).this.defun()

    Eq << algebra.imply.add_ge_zero.abs.minus.apply(f(x)) / 2

    Eq.fn_is_nonnegative =  Eq[-1].subs(Eq[-2].reversed)

    Eq << Eq[1] - Eq[3]

    Eq << Eq[-1].reversed

    Eq << Eq[-1].subs(x, x + d)

    Eq << Eq[0].subs(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(calculus.integral.to.add)

    Eq << Eq[-1].this.rhs.apply(calculus.integral.to.add)

    Eq << calculus.ge_zero.imply.eq.integral.limits.offset.apply(Eq.fp_is_nonnegative, Eq[-1].lhs.args[0], d)

    Eq << Eq[-2].subs(Eq[-1]).simplify()
    Eq << calculus.ge_zero.imply.eq.integral.limits.offset.apply(Eq.fn_is_nonnegative, Eq[-1].lhs, d)


if __name__ == '__main__':
    run()
# created on 2020-06-05
# updated on 2020-06-05
