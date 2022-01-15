from util import *


@apply(simplify=False)
def apply(self, index=0):
    [*args] = self.of(Mul)
    factor = args.pop(index)
    factor = -factor
   

    for i, arg in enumerate(args):
        if arg.is_Add:
            break
    else:
        return
    
    args[i] = Add(*[-arg for arg in arg.args])
    args.append(factor)
    
    return Equal(self, Mul(*args), evaluate=False)


@prove
def prove(Eq):
    a, b, c, d = Symbol(real=True)
    Eq << apply((a + b - c) * d)

    Eq << Eq[0].this.lhs.expand()
    
    Eq << Eq[-1].this.rhs.expand()

    

    

    

    
    


if __name__ == '__main__':
    run()
# created on 2021-08-02
# updated on 2021-12-16