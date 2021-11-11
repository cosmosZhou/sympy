from util import *




@apply
def apply(given):
    assert given.is_Unequal
    A, B = given.args
    if B:
        assert A.is_EmptySet
        A = B
    x = A.element_symbol()
    return Any[x](Element(x, A))


@prove
def prove(Eq):
    from axiom import sets

    A = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << sets.any_el.imply.ne_empty.apply(Eq[1])










if __name__ == '__main__':
    run()
# created on 2021-06-05
# updated on 2021-06-05
