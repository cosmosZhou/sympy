from util import *


@apply
def apply(given, f):
    x, s = given.of(Element)
    if x.is_given:
        z = s.generate_var(**x.type.dict)
        S = imageset(z, f(z), s)
    else:
        S = imageset(x, f(x), s)
    return Element(f(x), S)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol(integer=True)
    y = Symbol(integer=True, given=True)
    f = Function(integer=True)
    s = Symbol(etype=dtype.integer)

    Eq << apply(Element(y, s), f=f)

    S = Symbol(Eq[1].rhs)

    Eq << S.this.definition

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq.all_contains = All[x:s](Element(f(x), S), plausible=True)

    Eq << Eq.all_contains.this.expr.rhs.definition

    Eq << Eq[-1].this.expr.apply(sets.el.given.subset, simplify=False)

    Eq << sets.all_subset.given.subset.lhs.apply(Eq[-1])

    Eq << algebra.all.imply.ou.subs.apply(Eq.all_contains, x, y)

    Eq << algebra.cond.ou.imply.cond.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-07-29
