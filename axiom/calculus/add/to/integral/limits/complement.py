from util import *


def limits_complement(limits, _limits, function=None): 
    new_limits = []    
    assert len(limits) == len(_limits)
    
    for limit, _limit in zip(limits, _limits):
        x, domain = limit.coerce_setlimit(function=function)
        _x, _domain = _limit.coerce_setlimit(function=function)

        assert x == _x
        assert _domain in domain
        new_limits.append((x, domain - _domain))
        
    return new_limits


@apply
def apply(self):
    (function, *limits_a), (_function, *limits_b) = self.of(Sum - Sum)
    assert function == _function    
    limits = limits_complement(limits_a, limits_b, function=function)
    return Equal(self, Sum(function, *limits), evaluate=False)


@prove
def prove(Eq):
    k = Symbol.k(integer=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    f = Function.f(integer=True)
    Eq << apply(Add(Sum[k:A](f(k)), -Sum[k:A & B](f(k))))
    
    Eq << Eq[0] + Eq[0].find(-~Sum)
    
    
if __name__ == '__main__':
    run()
