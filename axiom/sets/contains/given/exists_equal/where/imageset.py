from sympy import *
from axiom.utility import prove, apply
import axiom
from sympy.sets.sets import image_set
from axiom import sets, algebre


@apply
def apply(imply):
    e, S = axiom.is_Contains(imply)

    image_set = S.image_set()
    
    expr, variables, base_set = image_set
    e = e.subs_limits_with_epitome(expr)            
    if e._has(variables):
        _variables = base_set.element_symbol(e.free_symbols)
        assert _variables.type == variables.type
        expr = expr._subs(variables, _variables)
        variables = _variables
    assert not e._has(variables)
    return Exists(Equality(e, expr, evaluate=False), (variables, base_set))


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    k = Symbol.k(integer=True)
    f = Function.f(integer=True)
    
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Contains(y, image_set(f(x), x, S)))
    
    Eq << Eq[1].simplify()
    
    Eq << algebre.imply.forall.limits_assert.apply(Eq[1].limits)
    
    Eq << Eq[-1].this.function.apply(sets.contains.imply.contains.imageset, f=f)
    
    Eq << Eq[-1].subs(Eq[1].reversed)
    
    
if __name__ == '__main__':
    prove(__file__)

