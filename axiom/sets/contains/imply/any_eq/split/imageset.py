from util import *
import axiom



@apply(simplify=False)
def apply(given):
    y, s = given.of(Contains)

    x, expr, base_set = axiom.is_ImageSet(s)

    return Exists[x:base_set](Equal(y, expr))


@prove
def prove(Eq):
    from axiom import sets
    y = Symbol.y(integer=True, given=True)
    x = Symbol.x(integer=True)
    f = Function.f(integer=True)

    S = Symbol.S(etype=dtype.integer, given=True)

    Eq << apply(Contains(y, imageset(x, f(x), S)))

    Eq << ~Eq[1]

    Eq << Eq[-1].this.function.apply(sets.ne.imply.notcontains)

    Eq << sets.all_notcontains.imply.notcontains.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]

if __name__ == '__main__':
    run()

