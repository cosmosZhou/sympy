from util import *


@apply
def apply(self):
    [*args], *limits = self.of(Integral[Add])
    
    rhs = Add(*(Integral(arg, *limits) for arg in args))
        
    return Equal(self, rhs, evaluate=False)


@prove(provable=False)
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    f = Function.f(real=True)
    h = Function.h(real=True)
    x = Symbol.x(real=True)
    Eq << apply(Integral[x:a:b](f(x) + h(x)))


if __name__ == '__main__':
    run()