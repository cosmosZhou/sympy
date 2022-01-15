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

    return eq, imply._subs(old, new)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(integer=True)
    S = Symbol(etype=dtype.integer)
    f = Function(integer=True)
    Eq << apply(NotElement(f(x), S) & Equal(x, y))

    Eq << Eq[-1].subs(Eq[-2].reversed)

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()


# created on 2018-06-10
