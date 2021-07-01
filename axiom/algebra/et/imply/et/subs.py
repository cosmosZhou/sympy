from util import *


@apply
def apply(given, index=None, reverse=False):
    eqs = given.of(And)

    if index is None:
        for eq in eqs:
            if eq.is_Equal:
                break
    else:
        eq = eqs[index]

    assert eq.is_Equal
    old, new = eq.args
    if reverse:
        old, new = new, old

    conds = []
    for cond in eqs:
        if cond is not eq:
            cond = cond._subs(old, new)
            conds.append(cond)

    return eq, And(*conds)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    b = Symbol.b(shape=(k,), real=True)
    Eq << apply(Unequal(x, y) & Unequal(f(x), g(y)) & Equal(f(x), b))

    Eq << algebra.et.imply.et.apply(Eq[0], index=1)

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq << Eq[-2].subs(Eq[1])

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()

