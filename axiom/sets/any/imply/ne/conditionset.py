from util import *


@apply
def apply(given):
    function, (x, S) = given.of(Any)    
    return Unequal(conditionset(x, function, S), x.emptySet)


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    f = Function.f(shape=(), integer=True)

    Eq << apply(Any[e:S](f(e) > 0))
    
    Eq << Any[e:S](Contains(e, Eq[-1].lhs), plausible=True)
    
    Eq << Eq[-1].this.function.simplify()
    
    Eq << Eq[-1].simplify()

    
if __name__ == '__main__':
    run()
