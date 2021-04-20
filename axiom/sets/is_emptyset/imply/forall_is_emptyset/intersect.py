from sympy.core.relational import Equal
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from axiom import sets
from sympy import ForAll, UNION
from sympy import Symbol

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

    if not x_union.is_UNION:
        tmp = x_union
        x_union = A
        A = tmp
    assert x_union.is_UNION

    return ForAll(Equal(x_union.function & A, A.etype.emptySet), *x_union.limits)




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    i = Symbol.i(integer=True)
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(shape=(k + 1,), etype=dtype.integer)

    Eq << apply(Equal(UNION[i:0:k](x[i]) & A, A.etype.emptySet))    
    
    Eq << Eq[-1].simplify()

    Eq << UNION[i:0:k](x[i] & A).this.simplify()

    Eq << Eq[-1].this.rhs.subs(Eq[0])
    
    Eq << Eq[-1].apply(sets.is_emptyset.imply.forall_is_emptyset.union_comprehension)


if __name__ == '__main__':
    prove()

