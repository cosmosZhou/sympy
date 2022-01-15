from util import *


@apply
def apply(imply):
    assert imply.is_Element
    x = imply.generate_var(**imply.lhs.type.dict)

    return Any[x:imply.rhs](Equal(imply.lhs, x))


@prove
def prove(Eq):
    x = Symbol(integer=True)

    S = Symbol(etype=dtype.integer)

    Eq << apply(Element(x, S))

    Eq << Eq[1].simplify()

if __name__ == '__main__':
    run()

# created on 2021-07-26
