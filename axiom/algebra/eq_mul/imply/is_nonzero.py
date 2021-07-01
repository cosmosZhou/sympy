from util import *


@apply
def apply(given): 
    (num, den), rhs = given.of(Equal[Expr / Expr, Expr])
        
    return Unequal(den, 0)


@prove(provable=False)
def prove(Eq):
    a = Symbol.a(complex=True)
    c = Symbol.c(complex=True)
    b = Symbol.b(complex=True)
    Eq << apply(Equal(a / b, c))

    

    


if __name__ == '__main__':
    run()