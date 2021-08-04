from util import *


from axiom.algebra.add_is_zero.given.et_eq.cubic.one_leaded import cubic_solve
from axiom.algebra.is_nonzero.add_is_zero.imply.ne import cubic_delta

def solver_set(d, A, B, x, alpha, beta, w):
    if d == 0:
        y = A + B    
    elif d % 3 == 1:
        y = A * w + B    
    elif d % 3 == 2:
        y = A * ~w + B    
    else:
        ...
        
    y0 = -2 * alpha / 3 + y
    y1 = 4 * alpha / 3 + y

    x0 = sqrt(2 * beta / sqrt(y0) - y1) / 2 - sqrt(y0) / 2
    x1 = -sqrt(2 * beta / sqrt(y0) - y1) / 2 - sqrt(y0) / 2
    x2 = sqrt(-2 * beta / sqrt(y0) - y1) / 2 + sqrt(y0) / 2
    x3 = -sqrt(-2 * beta / sqrt(y0) - y1) / 2 + sqrt(y0) / 2
        
    return Equal(x, x0) | Equal(x, x1) | Equal(x, x2) | Equal(x, x3)

@apply
def apply(fx, is_nonzero, x=None):
    from axiom.algebra.add_is_zero.imply.et.suffice.quartic.one_leaded import quartic_coefficient
    fx = fx.of(Equal[0])
    _1, _0, alpha, beta, gamma = quartic_coefficient(fx, x=x)
    assert _0 == 0 and _1 == 1
    
    w = -S.One / 2 + sqrt(3) * S.ImaginaryUnit / 2
    
    y_delta = cubic_delta(x, alpha, beta, gamma)
    _d, Y0, Y1, Y2 = cubic_solve(y_delta, x)
    
    _beta = is_nonzero.of(Unequal[0])
    assert _beta == beta

    delta = -(alpha ** 2 / 3 + 4 * gamma) ** 3 / 27 + (-alpha ** 3 / 27 + 4 * alpha * gamma / 3 - beta ** 2 / 2) ** 2

    V = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 - sqrt(delta)
    U = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 + sqrt(delta)
    
    A = U ** (S.One / 3)
    B = V ** (S.One / 3)
    
    return Suffice(Equal(_d, 0), solver_set(0, A, B, x, alpha, beta, w)), Suffice(Equal(_d % 3, 1), solver_set(1, A, B, x, alpha, beta, w)), Suffice(Equal(_d % 3, 2), solver_set(2, A, B, x, alpha, beta, w))


@prove
def prove(Eq):
    from axiom import algebra

    x, alpha, beta, gamma = Symbol(complex=True, given=True)
    fx = x ** 4 + alpha * x ** 2 + beta * x + gamma
    Eq << apply(Equal(fx, 0), Unequal(beta, 0), x=x)

    

    

    

    Eq << algebra.cond.imply.suffice.apply(Eq[0] & Eq[1], cond=Eq[2].lhs)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.add_is_zero.add_is_zero.is_nonzero.imply.ou_eq.quartic.depressed, x)

    Eq << algebra.cond.imply.suffice.apply(Eq[0] & Eq[1], cond=Eq[3].lhs)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.add_is_zero.mod_is_zero.is_nonzero.imply.ou_eq.quartic.depressed, x)

    Eq << algebra.cond.imply.suffice.apply(Eq[0] & Eq[1], cond=Eq[4].lhs)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.add_is_zero.mod_is_zero.is_nonzero.imply.ou_eq.quartic.depressed, x)

    #https://planetmath.org/QuarticFormula
    #https://en.wikipedia.org/wiki/Quartic_equation


if __name__ == '__main__':
    run()