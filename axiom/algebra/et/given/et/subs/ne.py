from util import *


@apply
def apply(imply, index=None):
    [*eqs] = imply.of(And)

    if index is None:
        for index, eq in enumerate(eqs):
            if eq.is_Unequal:
                break
        else:
            return

    eq = eqs.pop(index)

    imply = And(*eqs)

    old, new = eq.of(Unequal)
    old, new = KroneckerDelta(old, new), S.Zero

    return eq, imply._subs(old, new)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(integer=True)
    Eq << apply(NotContains(KroneckerDelta(x, y) + f(x), S) & Unequal(x, y))

    Eq << algebra.ne.imply.is_zero.kroneckerDelta.apply(Eq[1], simplify=None)

    Eq << Eq[0].subs(Eq[-1])
    Eq << algebra.et.given.et.apply(Eq[-1])


if __name__ == '__main__':
    run()