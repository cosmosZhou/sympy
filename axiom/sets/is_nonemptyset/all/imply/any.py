from util import *


@apply
def apply(is_nonemptyset, forall):
    S = is_nonemptyset.of(Unequal[EmptySet])
    function, (e, *rhs) = forall.of(All)
    
    if len(rhs) == 2:
        _S = Range(*rhs) if e.is_integer else Interval(*rhs)
    else:
        [_S] = rhs    
    assert S == _S
     
    return Any[e:S](function)


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.integer, given=True)
    e = Symbol.e(integer=True)
    f = Function.f(integer=True, shape=())
    Eq << apply(Unequal(S, S.etype.emptySet), All[e:S](f(e) > 0))
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[-1] & Eq[1]
    
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

