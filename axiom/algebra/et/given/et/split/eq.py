from util import *
from axiom.algebra.eq.cond.imply.cond.kronecker_delta import process_given_conditions
import axiom



@apply
def apply(imply, **kwargs):
    imply = imply.of(And)
    eq, cond = imply
    if not eq.is_Equal:
        eq, cond = cond, eq
    eq, f_eq = process_given_conditions(eq, cond, **kwargs)
    return And(eq, f_eq.simplify())


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    f = Function.f(nargs=(2,), shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    Eq << apply(Equal(x, y) & Unequal(g(KroneckerDelta(x, y)), f(x, y)))

    Eq << Equal(KroneckerDelta(x, y), 1, plausible=True)

    Eq << Eq[-1].simplify()

    Eq << algebra.et.imply.conds.apply(Eq[1])

    Eq << Eq[-1].subs(Eq[2].reversed)

    Eq <<= Eq[-1] & Eq[-3]


if __name__ == '__main__':
    run()

