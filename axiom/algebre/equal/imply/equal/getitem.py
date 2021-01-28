from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol, ForAll, Slice, Or
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from sympy.concrete.expr_with_limits import LAMBDA
from axiom import algebre, sets
from sympy.core.symbol import dtype


@apply(imply=True)
def apply(given, a, i=None):
    x, y = axiom.is_Equal(given)
    assert x.shape == y.shape    
    if i is None:
        return Equality(a[x], a[y])
    n = x.shape[0]
    return Equality(LAMBDA[i:n](a[x[i]]), LAMBDA[i:n](a[y[i]]))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    x = Symbol.x(shape=(n,), integer=True)
    y = Symbol.y(shape=(n,), integer=True)
    a = Symbol.a(shape=(n,), etype=dtype.integer)
    i = Symbol.i(integer=True)
    
    Eq << apply(Equality(x, y), a, i=i)
    
    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    prove(__file__)

