from util import *


@apply
def apply(*given):
    import axiom
    is_nonemptyset, forall = given
    S = is_nonemptyset.of(Unequal[EmptySet])
    function, *limits = forall.of(ForAll)
    e, _S = axiom.limit_is_set(limits)
    assert S == _S
     
    return Exists[e:S](function)


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.integer, given=True)
    e = Symbol.e(integer=True)
    f = Function.f(integer=True, shape=())
    Eq << apply(Unequal(S, S.etype.emptySet), ForAll[e:S](f(e) > 0))
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[-1] & Eq[1]
    
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

