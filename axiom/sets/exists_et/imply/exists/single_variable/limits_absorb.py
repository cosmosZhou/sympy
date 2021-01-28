
from axiom.utility import prove, apply

from sympy import *
import axiom
from axiom import sets


@apply(imply=True)
def apply(given, index):
    assert given.is_Exists and given.function.is_And
    
    eqs = [*given.function.args]
    eq = eqs[index]
    del eqs[index]
    wrt, B = axiom.is_Contains(eq)
    
    i = given.variables.index(wrt)
    
    function = And(*eqs)

    limits = [*given.limits]
    A = given.limits_dict[wrt]
    if A:
        limits[i] = (wrt, A & B)
    else:
        limits[i] = (wrt, B)

    return Exists(function, *limits)




@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)    
    x = Symbol.x(real=True, shape=(oo,))
    
    A = Symbol.A(etype=dtype.real * n)
    B = Symbol.B(etype=dtype.real * n)
    
    f = Function.f(nargs=(n,), shape=(), integer=True)

    Eq << apply(Exists[x[:n]: A](Contains(x[:n], B) & (f(x[:n]) > 0)), index=1)
    
    Eq << sets.exists.imply.exists_et.single_variable.apply(Eq[0])


if __name__ == '__main__':
    prove(__file__)

