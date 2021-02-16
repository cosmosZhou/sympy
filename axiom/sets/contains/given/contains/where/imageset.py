from axiom.utility import prove, apply
from sympy import *
import axiom

from axiom import sets, algebre
from sympy.sets.sets import imageset, image_set


@apply(given=True)
def apply(imply):
    e, S = axiom.is_Contains(imply)
    image_set = S.image_set()
    
    expr, variables, base_set = image_set

    variables_ = Wild(variables.name, **variables.type.dict)
    assert variables_.shape == variables.shape
    e = e.subs_limits_with_epitome(expr)
    dic = e.match(expr.subs(variables, variables_))
    
    variables_ = dic[variables_]
    return Contains(variables_, base_set)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    s = Symbol.s(etype=dtype.integer)
    
    Eq << apply(Contains(f(y), image_set(f(x), x, s)))
    
    Eq << sets.contains.imply.contains.imageset.apply(Eq[1], f=f)
    
if __name__ == '__main__':
    prove(__file__)

