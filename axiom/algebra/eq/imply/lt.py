from util import *


@apply
def apply(given, b):    
    x, y = given.of(Equal)
    assert y < b
    return Less(x, b)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Equal(a, b), b + 1)
    
    Eq << Eq[1].subs(Eq[0])
    
    
if __name__ == '__main__':
    run()
