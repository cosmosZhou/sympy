from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply(simplify=False)
def apply(self):
    args = []    
    for arg in axiom.is_Add(self):
        if arg.is_Add:
            args += arg.args
        else:
            args.append(arg)
    
    return Equal(self, Add(*args), evaluate=False)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Add(Add(a, b), x, evaluate=False))
    
    Eq << Eq[-1] - x

    
if __name__ == '__main__':
    prove()
