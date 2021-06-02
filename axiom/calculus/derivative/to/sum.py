from util import *

import axiom


@apply
def apply(self):
    function, *limits_d = self.of(Derivative)
    f, *limits_s = function.of(Sum)
    
    return Equal(self, Sum(Derivative(f, *limits_d).doit(), *limits_s))


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(real=True)    
    n = Symbol.n(integer=True)
    Eq << apply(Derivative[x](Sum[n:0:oo](f[n](x))))


if __name__ == '__main__':
    run()

