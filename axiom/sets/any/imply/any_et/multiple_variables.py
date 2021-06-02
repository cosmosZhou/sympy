


from util import *


import axiom



@apply
def apply(given):
    function, *limits = given.of(Exists)
    variables = axiom.limits_are_Contains(limits)    
    return Exists[variables](And(function, given.limits_cond).simplify())




@prove
def prove(Eq):    
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    f = Function.f(nargs=(2,), shape=(), integer=True)

    Eq << apply(Exists[x:A, y:B](f(x, y) > 0))
    
    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

