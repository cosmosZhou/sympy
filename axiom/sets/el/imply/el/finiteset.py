from util import *



@apply
def apply(given, t):
    assert given.is_Element

    e, finiteset = given.args

    args = finiteset.of(FiniteSet)

    finiteset = finiteset.func(*(arg + t for arg in args))

    return Element(e + t, finiteset)


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol(integer=True)
    a, b, t = Symbol(real=True)

    Eq << apply(Element(x, {a, b}), t)

    Eq << sets.el.imply.ou.split.finiteset.two.apply(Eq[0], simplify=None)

    Eq << Eq[-1].this.args[0] + t

    Eq << Eq[-1].this.args[1] + t

    Eq << sets.ou_eq.imply.el.finiteset.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-03-04
