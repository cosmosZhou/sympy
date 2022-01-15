from util import *



@apply(given=None)
def apply(given, index=None, invert=False):
    p, q = given.of(Infer)
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
    return Equivalent(given, Infer(p, q), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    f, g = Function(real=True)

    Eq << apply(Infer(Equal(f(x), x + 1) & Element(x, A),
                           Equal(Piecewise((g(x), Equal(f(x), x + 1)), (g(y), True)), y)),
                           index=0)

    Eq << Equivalent(Infer(Equal(f(x), x + 1) & Element(x, A),
                                Equal(Piecewise((g(x), Equal(f(x), x + 1)), (g(y), True)), y)),

                     Infer(Equal(Bool(Equal(f(x), x + 1)), 1) & Element(x, A),
                                Equal(Piecewise((g(x), Equal(Bool(Equal(f(x), x + 1)), 1)), (g(y), True)), y)),

                     plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[1].this.rhs.apply(algebra.infer.subs)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)


if __name__ == '__main__':
    run()
# created on 2019-10-06
