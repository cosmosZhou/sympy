from axiom.utility import prove, apply
from sympy import *
from axiom import sets, algebra


@apply
def apply(self):
    image_set = self.image_set()
    variables, expr, base_set = image_set

    if isinstance(base_set, Symbol):
        return ForAll(Contains(expr, self), (variables, base_set))

@prove
def prove(Eq):
    e = Symbol.e(etype=dtype.integer.set)
    s = Symbol.s(etype=dtype.integer.set.set)
    f = Function.f(etype=dtype.integer.set)
    S = Symbol.S(imageset(e, f(e), s))    
    Eq << apply(S)
    
    Eq << algebra.forall.given.sufficient.apply(Eq[1])
    
    Eq << Eq[-1].this.lhs.apply(sets.contains.imply.contains.imageset, f)
    
    Eq << Eq[-1].this.rhs.rhs.definition


if __name__ == '__main__':
    prove()

