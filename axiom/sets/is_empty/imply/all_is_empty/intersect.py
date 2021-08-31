from util import *


@apply
def apply(given):
    x_union, A = given.of(Equal[Intersection, EmptySet])
    if not x_union.is_Cup:
        x_union, A = A, x_union
        
    expr, *limits = x_union.of(Cup)
    return All(Equal(expr & A, A.etype.emptySet), *limits)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol(etype=dtype.integer)
    i = Symbol(integer=True)
    k = Symbol(integer=True, positive=True)
    x = Symbol(shape=(k + 1,), etype=dtype.integer)

    Eq << apply(Equal(Cup[i:0:k](x[i]) & A, A.etype.emptySet))

    Eq << Eq[-1].simplify()

    Eq << Cup[i:0:k](x[i] & A).this.simplify()

    Eq << Eq[-1].this.rhs.subs(Eq[0])

    Eq << Eq[-1].apply(sets.is_empty.imply.all_is_empty.cup)


if __name__ == '__main__':
    run()

