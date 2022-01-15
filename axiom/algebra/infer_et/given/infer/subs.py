from util import *


@apply
def apply(given, index=None):
    et, f = given.of(Infer)
    eqs = et.of(And)
    if index is None:
        for index, eq in enumerate(eqs):
            if eq.is_Equal:
                break

    eq = eqs[index]
    old, new = eq.of(Equal)

    return Infer(et, f._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True)
    t, f, g = Function(integer=True)
    Eq << apply(Infer(Equal(t(x), y) & (f(x) > y), Equal(f(t(x), y), g(x))))

    Eq << algebra.infer.given.infer.et.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.eq, index=2)


if __name__ == '__main__':
    run()
# created on 2018-06-11
