from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self):
    for i, eq in enumerate(self.args):
        if isinstance(eq, And):
            args = [*self.args]
            del args[i]
            this = self.func(*args)
            return And(*((arg | this).simplify() for arg in eq.args))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)
    
    f = Function.f(shape=(k,), real=True)
    g = Function.g(shape=(k,), real=True)
    
    Eq << apply(Or(Unequal(x, y) & (y > 0), Equal(f(x), g(y))))
    
    Eq << algebra.et.imply.ou.collect.apply(Eq[1], cond=Equal(f(x), g(y)))


if __name__ == '__main__':
    prove()

del collect
from . import collect
