from util import *



@apply
def apply(given):
    contains, *limits = given.of(Any)
    x, A = contains.of(Element)
    return Unequal(A, A.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol(etype=dtype.real, given=True)
    e = Symbol(real=True)

    Eq << apply(Any[e](Element(e, A)))

    Eq << sets.ne_empty.imply.any_el.apply(Eq[1])


if __name__ == '__main__':
    run()

# created on 2018-09-06
