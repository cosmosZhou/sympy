from util import *
import axiom



@apply(simplify=False)
def apply(self):
    args = []    
    for arg in self.of(Mul):
        if arg.is_Mul:
            args += arg.args
        else:
            args.append(arg)
    
    return Equal(self, Mul(*args), evaluate=False)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Mul(Mul(a, b), x, evaluate=False))
    
    y = Symbol.y(a * b)
    
    Eq << y.this.definition
    
    Eq << Eq[-1] * x
    
    Eq << Eq[0].subs(Eq[-1].reversed)
    
    Eq << Eq[-1].subs(Eq[1].reversed)

    
if __name__ == '__main__':
    run()
