
from axiom.utility import plausible

from sympy import Symbol
from sympy import Exists
from sympy.core.function import Function
from sympy.logic.boolalg import And
from sympy.core.numbers import oo
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
import axiom
from axiom import sets


@plausible
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
    assert A.is_set
    
    limits[i] = (wrt, A & B)

    return Exists(function, *limits)


from axiom.utility import check


@check
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

