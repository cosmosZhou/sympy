from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol, Dummy, Slice, Or, log, Sum
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from sympy.concrete.expr_with_limits import LAMBDA
from axiom import algebre, sets
from sympy.functions.special.tensor_functions import KroneckerDelta


@apply(imply=True)
def apply(given, x, y):
    axiom.is_Equal(given)
    
    d = Dummy(**y.type.dict)
    this = given._subs(x, d)
    this = this._subs(y, x)
    return this._subs(d, y)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    x = Symbol.x(shape=(n,), real=True)
    y = Symbol.y(shape=(n,), real=True)
    
    Eq << apply(Equality(x @ y, Sum[j:n, i:n](KroneckerDelta(i, j) * x[j] * y[i])), x, y)
    
    z = Symbol.z(shape=(n,), real=True)
    Eq << Eq[0].subs(x, z)
    
    Eq << Eq[-1].subs(y, x)
    
    Eq << Eq[-1].subs(z, y)


if __name__ == '__main__':
    prove(__file__)

