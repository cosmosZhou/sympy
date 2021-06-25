from util import *


@apply
def apply(self): 
    args = self.of(Exp[Add])    
    
    args = [exp(e) for e in args]
        
    return Equal(self, Mul(*args), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    b = Symbol.b(real=True)
    a = Symbol.a(real=True)
    Eq << apply(exp(a + b))

    Eq << algebra.eq.given.eq.log.apply(Eq[-1])
    Eq << Eq[-1].this.rhs.apply(algebra.log.to.add)


if __name__ == '__main__':
    run()