from util import *
import axiom



# given: f(a) != f(b) or a = b
# ForAll[a: a!=b](f(a) != f(b))
@apply
def apply(given, pivot=0):
    [*conds] = given.of(Or)

    if isinstance(pivot, tuple):
        eq = []
        for i in sorted(pivot, reverse=True):
            eq.append(conds.pop(i))
        eq = Or(*eq)
    else:
        eq = conds.pop(pivot)

    cond = eq.invert()

    return Suffice(cond, given.func(*conds))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    y = Symbol.y(complex=True, shape=(n,))

    f = Function.f(complex=True, shape=())
    g = Function.g(complex=True, shape=())

    Eq << apply(Unequal(f(x), 1) | Unequal(g(x), 1) | Equal(x, y), pivot=(0, 1))

    Eq << Eq[1].apply(algebra.suffice.given.ou)


if __name__ == '__main__':
    run()

