from util import *


@apply
def apply(self, var=None):
    fx, (x, d) = self.of(Derivative)
    assert d == 1
    if var is None:
        var = self.generate_var(var='epsilon', real=True)
    
    assert not self._has(var)
    
    return Equal(self, Limit[var:0]((fx._subs(x, x + var) - fx) / var))

    
@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(real=True)
    epsilon = Symbol.epsilon(real=True)
    Eq << apply(Derivative(f(x), x), var=epsilon)

    


if __name__ == '__main__':
    run()
