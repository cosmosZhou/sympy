from util import *



@apply
def apply(given, t):
    assert given.is_Contains

    e, finiteset = given.args

    args = finiteset.of(FiniteSet)

    finiteset = finiteset.func(*(arg + t for arg in args))

    return Contains(e + t, finiteset)


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(integer=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    t = Symbol.t(real=True)

    Eq << apply(Contains(x, {a, b}), t)

    Eq << sets.contains.imply.ou.split.finiteset.two.apply(Eq[0], simplify=None)

    Eq << Eq[-1].this.args[0] + t

    Eq << Eq[-1].this.args[1] + t

    Eq << sets.ou.imply.contains.finiteset.apply(Eq[-1])


if __name__ == '__main__':
    run()

