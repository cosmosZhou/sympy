from util import *



def process_given_conditions(*given, invert=None, reverse=False, swap=False):
    if swap:
        f_eq, eq = given
    else:
        eq, f_eq = given

    assert eq.is_Boolean
    assert f_eq.is_Boolean

    eq_original = eq
    if invert:
        eq = eq.invert()
        substituent = S.BooleanFalse
    else:
        substituent = S.BooleanTrue

    if reverse:
        eq = eq.reversed

    return eq_original, f_eq._subs(eq, substituent)


@apply
def apply(*given, **kwargs):
    eq, f_eq = process_given_conditions(*given, **kwargs)
    return f_eq


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    h = Function.h(shape=(), integer=True)

    Eq << apply(NotContains(x, S), Equal(Piecewise((f(x), NotContains(x, S)), (g(x), True)), h(x)))

    Eq << Equal(Bool(NotContains(x, S)), 1, plausible=True)

    Eq << Eq[-1].this.lhs.apply(algebra.bool.to.piecewise)

    Eq << Equal(Piecewise((f(x), Equal(Bool(NotContains(x, S)), 1)), (g(x), True)), h(x), plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[1].this.lhs.simplify()

    Eq << Eq[-2].subs(Eq[-3])


if __name__ == '__main__':
    run()

