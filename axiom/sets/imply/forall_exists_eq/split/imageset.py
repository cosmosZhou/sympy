from axiom.utility import prove, apply
from sympy import *
from axiom import sets, algebra


@apply
def apply(self):
    image_set = self.image_set()
    variables, expr, base_set = image_set

    if isinstance(base_set, Symbol):
        element_symbol = self.element_symbol()
        assert expr.type == element_symbol.type
        condition = Equal(expr, element_symbol)
        return ForAll(Exists(condition, (variables, base_set)), (element_symbol, self))


@prove
def prove(Eq):
    e = Symbol.e(etype=dtype.integer.set)
    s = Symbol.s(etype=dtype.integer.set.set)
    f = Function.f(etype=dtype.integer.set)
    S = Symbol.S(imageset(e, f(e), s))    
    Eq << apply(S)
    
    Eq << algebra.forall.given.sufficient.apply(Eq[1])
    
    Eq << Eq[-1].this.args[0].apply(sets.contains.imply.exists_eq.split.imageset)
    
    Eq << Eq[-1].this.args[0].function.reversed


if __name__ == '__main__':
    prove()

