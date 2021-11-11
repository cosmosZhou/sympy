from util import *



@apply
def apply(S):
    assert S.is_set

    e = S.element_symbol()
    return Any(Element(e, S), (e,)) | Equal(S, e.emptySet)


@prove
def prove(Eq):
    from axiom import sets, algebra
    S = Symbol(etype=dtype.real)

    Eq << apply(S)

    Eq << Eq[-1].apply(algebra.cond.given.et.all, cond=Unequal(S, S.etype.emptySet))

    Eq << Eq[-1].this.expr.apply(sets.any_el.given.ne_empty)


if __name__ == '__main__':
    run()

# created on 2018-09-06
# updated on 2018-09-06
