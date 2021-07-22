from util import *

# given: A & Union[i](x[i]) = {}
# A & x[i] = {}


@apply
def apply(given):
    assert given.is_Equal
    x_union_intersect_A, emptyset = given.args
    if emptyset:
        tmp = emptyset
        emptyset = x_union_intersect_A
        x_union_intersect_A = tmp
        assert emptyset.is_EmptySet

    assert x_union_intersect_A.is_Intersection
    x_union, A = x_union_intersect_A.args

    if not x_union.is_Cup:
        tmp = x_union
        x_union = A
        A = tmp
    assert x_union.is_Cup

    return All(Equal(x_union.expr & A, A.etype.emptySet), *x_union.limits)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer)
    i = Symbol.i(integer=True)
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(shape=(k + 1,), etype=dtype.integer)

    Eq << apply(Equal(Cup[i:0:k](x[i]) & A, A.etype.emptySet))

    Eq << Eq[-1].simplify()

    Eq << Cup[i:0:k](x[i] & A).this.simplify()

    Eq << Eq[-1].this.rhs.subs(Eq[0])

    Eq << Eq[-1].apply(sets.is_emptyset.imply.all_is_emptyset.cup)


if __name__ == '__main__':
    run()

