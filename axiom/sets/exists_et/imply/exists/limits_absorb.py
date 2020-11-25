
from axiom.utility import plausible

from sympy import Symbol
from sympy.concrete.expr_with_limits import Exists
from sympy.core.function import Function
from sympy.logic.boolalg import And


@plausible
def apply(given, index):
    assert given.is_Exists and given.function.is_And
    
    eqs = [*given.function.args]
    eq = eqs[index]
    del eqs[index]
    
    function = And(*eqs)
    variables = given.variables
    wrt = {v for v in variables if eq._has(v)}
        
    assert wrt
    limits = [*given.limits]
    if len(wrt) == 1:
        wrt, *_ = wrt
        i = variables.index(wrt)        
        wrt, *ab = limits[i]
        assert ab 
        limits[i] = (wrt, eq)
    elif len(wrt) == 2:
        x_slice, x_index = wrt
        if x_slice.is_Indexed:
            x_slice, x_index = x_index, x_slice
             
        assert x_slice.is_Slice and x_index.is_Indexed
        start, stop = x_slice.indices
        assert len(x_index.indices) == 1
        assert x_index.indices[0] == stop
        i = variables.index(x_slice)
        j = variables.index(x_index)
        
        del limits[j]
        wrt, cond = limits[i]  
        wrt = x_slice.base[start:stop + 1]              
        limits[i] = (wrt, cond & eq)        
    else:
        return 
        
    return Exists(function, *limits, given=given)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,))
    
    f = Function.f(nargs=(n,), shape=(), integer=True)
    f_quote = Function("f'", nargs=(n,), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)
    h = Function.h(nargs=(n + 1,), shape=(), integer=True)

    Eq << apply(Exists[x[:n]:f(x[:n]) > 0, x[n]]((g(x[n]) > f_quote(x[:n])) & (h(x[:n + 1]) > 0)), index=0)


if __name__ == '__main__':
    prove(__file__)

