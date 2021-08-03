from util import *


@apply
def apply(is_zero, n=None):
    x = is_zero.of(Equal[Cos, 0])    
    if n is None:
        n = is_zero.generate_var(integer=True, var='n')
    assert Integers in n.domain
    return Any[n](Equal(x, S.Pi / 2 + S.Pi * n))


@prove
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(Equal(cos(x), 0))

    

    

    

    #https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()