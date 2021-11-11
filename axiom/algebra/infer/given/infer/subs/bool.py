from util import *


@apply
def apply(given, invert=False):
    eq, f = given.of(Infer)
    if invert:
        old = eq.invert()
        new = S.false
    else:
        old = eq
        new = S.true

    return Infer(eq, f._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra

    y, x = Symbol(integer=True)
    A = Symbol(etype=dtype.integer)
    t, f, g = Function(integer=True)
    Eq << apply(Infer(Element(t(x), A), Equal(Piecewise((f(t(x), y), Element(t(x), A)), (g(x), True)), g(x))))

    Eq << algebra.infer.given.infer.et.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.bool, index=1)


if __name__ == '__main__':
    run()
# created on 2018-06-14
# updated on 2018-06-14
