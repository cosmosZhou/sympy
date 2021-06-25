from util import *



@apply
def apply(imply, index=None, reverse=False):
    [*eqs] = imply.of(And)

    if index is None:
        for index, eq in enumerate(eqs):
            if eq.is_Equal:
                break
        else:
            return

    eq = eqs.pop(index)

    imply = And(*eqs)

    old, new = eq.of(Equal)

    if reverse:
        old, new = new, old

    return imply._subs(old, new) & eq


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(integer=True)

    Eq << apply(NotContains(f(x), S) & Equal(x, y))

    Eq << algebra.et.imply.conds.apply(Eq[1])

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq <<= Eq[-1] & Eq[-2]

if __name__ == '__main__':
    run()


