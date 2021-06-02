from util import *
import axiom



@apply(given=None)
def apply(given, index=None, invert=False):
    p, q = given.of(Suffice)
    if index is None:
        cond = p
    else:
        eqs = p.of(And)
        cond = eqs[index]

    if invert:
        old = cond.invert()
        new = S.false
    else:
        old = cond
        new = S.true

    q = q._subs(old, new)
    return Equivalent(given, Suffice(p, q), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    A = Symbol.A(etype=dtype.real)
    f = Function.f(real=True)
    g = Function.g(real=True)

    Eq << apply(Suffice(Equal(f(x), x + 1) & Contains(x, A),
                           Equal(Piecewise((g(x), Equal(f(x), x + 1)), (g(y), True)), y)),
                           index=0)

    Eq << Equivalent(Suffice(Equal(f(x), x + 1) & Contains(x, A),
                                Equal(Piecewise((g(x), Equal(f(x), x + 1)), (g(y), True)), y)),

                     Suffice(Equal(Bool(Equal(f(x), x + 1)), 1) & Contains(x, A),
                                Equal(Piecewise((g(x), Equal(Bool(Equal(f(x), x + 1)), 1)), (g(y), True)), y)),

                     plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[1].this.rhs.apply(algebra.suffice.subs)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)


if __name__ == '__main__':
    run()
