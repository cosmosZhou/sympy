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

    y = Symbol.y(integer=True)
    x = Symbol.x(integer=True)
    A = Symbol.A(etype=dtype.integer)
    t = Function.t(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    Eq << apply(Suffice(Contains(t(x), A), Equal(Piecewise((f(t(x), y), Contains(t(x), A)), (g(x), True)), g(x))))

    Eq << algebra.suffice.given.suffice.et.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.bool, index=1)


if __name__ == '__main__':
    run()