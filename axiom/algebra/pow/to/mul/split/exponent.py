from util import *
import axiom



@apply
def apply(self): 
    base, exponent = self.of(Pow)
    exponent = exponent.of(Add)
    
    args = [base ** e for e in exponent]
        
    return Equal(self, Mul(*args), evaluate=False)


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True, positive=True)
    
    b = Symbol.b(real=True, positive=True)

    a = Symbol.a(real=True, positive=True)

    Eq << apply(x ** (a + b))   
    
if __name__ == '__main__':
    run()
