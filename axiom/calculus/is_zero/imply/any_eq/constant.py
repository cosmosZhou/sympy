from util import *
import axiom



@apply
def apply(given):
    dfx = given.of(Equal[0])
    fx, *limits = dfx.of(Derivative)
    C = given.generate_var(real=True, var='C')
    return Exists[C](ForAll(Equal(fx, C), *((x,) for x,*_ in limits)))


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(real=True)    
    
    Eq << apply(Equal(Derivative[x](f(x)), 0))

    
if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function#Properties

