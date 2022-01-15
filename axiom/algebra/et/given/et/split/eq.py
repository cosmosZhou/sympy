from util import *


@apply
def apply(imply, **kwargs):
    from axiom.algebra.eq.cond.imply.cond.kroneckerDelta import process_given_conditions
    imply = imply.of(And)
    eq, cond = imply
    if not eq.is_Equal:
        eq, cond = cond, eq
    eq, f_eq = process_given_conditions(eq, cond, **kwargs)
    return eq, f_eq.simplify()


@prove
def prove(Eq):
    x, y = Symbol(integer=True, given=True)
    f, g = Function(shape=(), integer=True)
    Eq << apply(Equal(x, y) & Unequal(g(KroneckerDelta(x, y)), f(x, y)))

    Eq << Equal(KroneckerDelta(x, y), 1, plausible=True)

    Eq << Eq[-1].simplify()

    Eq << Eq[2].subs(Eq[-1].reversed)

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

# created on 2019-02-27
