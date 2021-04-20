from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self): 
    for i, union in enumerate(self.args):
        if isinstance(union, INTERSECTION):
            args = [*self.args]
            del args[i]
            this = self.func(*args)
            function = union.function | this
            return Equal(self, union.func(function, *union.limits), evaluate=False)


@prove
def prove(Eq):
    x = Symbol.x(etype=dtype.integer)
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(etype=dtype.integer)
    Eq << apply(INTERSECTION[k:n](f(k)) | x)
    return
    Eq << Eq[-1].this.rhs.simplify()

    
if __name__ == '__main__':
    prove()
