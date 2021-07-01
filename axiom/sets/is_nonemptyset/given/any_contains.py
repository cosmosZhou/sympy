from util import *




@apply
def apply(given):
    assert given.is_Unequal
    A, B = given.args
    if B:
        assert A.is_EmptySet
        A = B
    x = A.element_symbol()
    return Any[x](Contains(x, A))


@prove
def prove(Eq):
    from axiom import sets

    A = Symbol.A(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << sets.any_contains.imply.is_nonemptyset.apply(Eq[1])

    

    

    

    


if __name__ == '__main__':
    run()