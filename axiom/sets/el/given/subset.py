from util import *



# given: A in B
# => {A} subset B
@apply
def apply(given):
    assert given.is_Element
    e, s = given.args

    return Subset(e.set, s)


@prove
def prove(Eq):
    from axiom import sets
    e = Symbol(integer=True)
    s = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, s, evaluate=False))

    Eq << sets.subset.imply.el.apply(Eq[1])

if __name__ == '__main__':
    run()

# created on 2020-07-27
# updated on 2020-07-27
