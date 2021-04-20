from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra
from axiom.sets.contains.given.contains.split.imageset import subs_limits_with_epitome


@apply
def apply(imply):
    e, S = axiom.is_Contains(imply)

    image_set = S.image_set()
    
    variables, expr, base_set = image_set
    e = subs_limits_with_epitome(e, expr)            
    if e._has(variables):
        _variables = base_set.element_symbol(e.free_symbols)
        assert _variables.type == variables.type
        expr = expr._subs(variables, _variables)
        variables = _variables
    assert not e._has(variables)
    return Exists(Equal(e, expr, evaluate=False), (variables, base_set))


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Contains(y, imageset(x, f(x), S)))
    
    Eq << Eq[1].simplify()
    
    Eq << algebra.imply.forall.limits_assert.apply(Eq[1].limits)
    
    Eq << Eq[-1].this.function.apply(sets.contains.imply.contains.imageset, f=f)
    
    Eq << algebra.exists_eq.forall.imply.exists.subs.apply(Eq[1].reversed, Eq[-1])
    
    
if __name__ == '__main__':
    prove()

