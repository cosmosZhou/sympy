from util import *


@apply
def apply(given, invert=False):
    eq, f = given.of(Suffice)
    if invert:
        old = eq.invert()
        new = S.false
    else:
        old = eq
        new = S.true

    return Suffice(eq, f._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra

    y, x = Symbol(integer=True)
    A = Symbol(etype=dtype.integer)
    t, f, g = Function(integer=True)
    Eq << apply(Suffice(Element(t(x), A), Equal(Piecewise((f(t(x), y), Element(t(x), A)), (g(x), True)), g(x))))

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(algebra.cond.cond.imply.cond.subs, swap=True)


if __name__ == '__main__':
    run()
