from util import *



@apply
def apply(r, x=None, n=None):
    assert r.is_real
    if x is None:
        x = Symbol.x(real=True)
        
    if n is None:
        n = Symbol.n(integer=True)
        
    return Equal((1 + x) ** r, Sum[n:0:oo](binomial(r, n) * x ** n))


@prove(proved=False)
def prove(Eq):
    x, r = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(r, x=x, n=n)


if __name__ == '__main__':
    run()

# created on 2020-10-20
# updated on 2020-10-20
