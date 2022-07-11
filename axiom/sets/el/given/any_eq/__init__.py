from util import *


@apply(simplify=False)
def apply(imply, var=None):
    assert imply.is_Element
    if var is None:
        var = imply.generate_var(**imply.lhs.type.dict)
    elif isinstance(var, str):
        var = imply.generate_var(var=var, **imply.rhs.etype.dict)

    return Any[var:imply.rhs](Equal(imply.lhs, var))


@prove
def prove(Eq):
    x = Symbol(integer=True)
    S = Symbol(etype=dtype.integer)
    Eq << apply(Element(x, S))

    Eq << Eq[1].simplify()

    
    


if __name__ == '__main__':
    run()

# created on 2021-07-26

from . import split
# updated on 2022-04-03
