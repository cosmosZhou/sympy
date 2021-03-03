from axiom.utility import prove, apply
from sympy import *
import axiom

from axiom import sets, algebre


@apply
def apply(imply):
    e, S = axiom.is_Contains(imply)
    image_set = S.image_set()
    
    variables, expr, base_set = image_set

    variables_ = Wild(variables.name, **variables.type.dict)
    assert variables_.shape == variables.shape
    e = e.subs_limits_with_epitome(expr)
    dic = e.match(expr.subs(variables, variables_))
    
    variables_ = dic[variables_]
    if variables_.shape != variables.shape:
        indices = [slice(0, length) for length in variables.shape]
        variables_ = variables_[indices]
            
    assert variables_.shape == variables.shape
    return Contains(variables_, base_set)

@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    s = Symbol.s(etype=dtype.integer)
    
    Eq << apply(Contains(f(y), imageset(x, f(x), s)))
    
    Eq << sets.contains.imply.contains.imageset.apply(Eq[1], f=f)
    
if __name__ == '__main__':
    prove(__file__)

