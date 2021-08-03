from util import *


@apply
def apply(eq, f_eq, index=None, reverse=False, swap=False):
    if swap:
        eq, f_eq = f_eq, eq

    old, new = eq.of(Equal)

    if reverse:
        old, new = new, old

    return eq, f_eq._subs(old, new)


@prove
def prove(Eq):
    x, y = Symbol(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f, g = Function(integer=True)
    Eq << apply(Equal(f(x), g(y)), Equal(x, y), swap=True)

    Eq << Eq[0].subs(Eq[1])

    


if __name__ == '__main__':
    run()