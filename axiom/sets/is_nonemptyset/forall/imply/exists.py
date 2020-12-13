from sympy.core.relational import Unequality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import Exists, ForAll
from sympy import Symbol
import axiom
from sympy.core.function import Function


@plausible
def apply(*given):
    is_nonemptyset, forall = given
    S = axiom.is_nonemptyset(is_nonemptyset)
    function, *limits = axiom.is_ForAll(forall)
    e, _S = axiom.limits_is_set(limits).args
    assert S == _S
     
    return Exists[e:S](function)


from axiom.utility import check


@check
def prove(Eq):
    S = Symbol.S(etype=dtype.integer)
    e = Symbol.e(integer=True)
    f = Function.f(integer=True, shape=())
    Eq << apply(Unequality(S, S.etype.emptySet), ForAll[e:S](f(e) > 0))
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[-1] & Eq[1]
    
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    prove(__file__)

