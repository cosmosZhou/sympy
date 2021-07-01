from util import *


@apply
def apply(self, index=-1):
    [*args] = self.of(Or)
    for i, eq in enumerate(args):
        if isinstance(eq, And):
            break
    else:
        return
    
    del args[i]
    this = self.func(*args)
    args = eq.args
    lhs = And(*args[:index])
    rhs = And(*args[index:])
    
    return (lhs | this).simplify(), (rhs | this).simplify()


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)
    f = Function.f(shape=(k,), real=True)
    g = Function.g(shape=(k,), real=True)
    Eq << apply(Or(Unequal(x, y) & (y > 0), Equal(f(x), g(y))))

    

    Eq << Eq[0].this.args[1].apply(algebra.et.imply.cond, index=1)

    Eq << Eq[0].this.args[1].apply(algebra.et.imply.cond, index=0)


if __name__ == '__main__':
    run()

del collect
from . import collect
