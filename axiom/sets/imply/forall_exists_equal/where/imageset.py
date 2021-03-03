
from axiom.utility import prove, apply
from sympy import *
from axiom import sets, algebre


@apply
def apply(self):
    image_set = self.image_set()
    variables, expr, base_set = image_set

    if isinstance(base_set, Symbol):
        element_symbol = self.element_symbol()
        assert expr.type == element_symbol.type
        condition = Equality(expr, element_symbol)
        return ForAll(Exists(condition, (variables, base_set)), (element_symbol, self))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    e = Symbol.e(etype=dtype.integer.set)
    s = Symbol.s(etype=dtype.integer.set.set)
    B = Symbol.B(imageset(e, e | {n.set}, s))    
    Eq << apply(B)


if __name__ == '__main__':
    prove(__file__)
