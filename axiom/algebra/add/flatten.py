from util import *
import axiom



@apply(simplify=False)
def apply(self):
    args = []    
    for arg in self.of(Add):
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
    run()
