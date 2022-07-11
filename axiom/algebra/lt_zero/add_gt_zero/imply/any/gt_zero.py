from util import *


@apply
def apply(lt_zero, gt_zero, x=None):
    a = lt_zero.of(Expr < 0)
    b, (S[a], c) = gt_zero.of(Expr ** 2 - 4 * Expr * Expr > 0)
    assert x.is_real
    assert a.is_real and b.is_real and c.is_real
    return Any[x](a * x ** 2 + b * x + c > 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a < 0, b ** 2 - 4 * a * c > 0, x=x)

    a = Symbol(-a)
    b = Symbol(-b)
    c = Symbol(-c)
    Eq.a_def = a.this.definition

    Eq.b_def = b.this.definition

    Eq.c_def = c.this.definition

    Eq << -Eq[0].subs(-Eq.a_def.reversed)

    Eq << Eq[1].subs(-Eq.a_def.reversed, -Eq.b_def.reversed, -Eq.c_def.reversed)

    Eq << algebra.gt_zero.add_gt_zero.imply.any.lt_zero.apply(Eq[-2], Eq[-1], x=x)

    Eq << -Eq[-1].this.expr

    Eq << Eq[-1].subs(Eq.a_def, Eq.b_def, Eq.c_def)


if __name__ == '__main__':
    run()
# created on 2022-04-03
