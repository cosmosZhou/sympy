from util import *

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(piecewise, var):
    (expr, cond), (expr_else, _) = piecewise.of(Piecewise)
    eqs = cond.of(And)

    var_eqs = []
    non_var_eqs = []

    for eq in eqs:
        if eq._has(var):
            var_eqs.append(eq)
        else:
            non_var_eqs.append(eq)

    var_eqs = And(*var_eqs)
    non_var_eqs = And(*non_var_eqs)

    return Equal(piecewise, Piecewise((Piecewise((expr, non_var_eqs), (expr_else, True)), var_eqs), (expr_else, True)))


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,))

    A, B = Symbol(etype=dtype.real * k)
    f, g, h = Function(shape=(), real=True)

    Eq << apply(Piecewise((f(x) * g(y), Element(x, A) & Element(y, B)), (h(x, y), True)), var=y)

    Eq << Eq[0].this.rhs.apply(algebra.piece.flatten, index=0)


if __name__ == '__main__':
    run()

# created on 2020-02-22
# updated on 2020-02-22
