from util import *


@apply
def apply(self):
    b, e = self.of(Expr ** Expr)
    assert not b.shape and e.shape
    [*args] = e.of(Mul)
    for i, one in enumerate(args):
        if one.is_OneMatrix:
            break
    else:
        return
    del args[i]
    e = Mul(*args)
    assert not e.shape
    b *= one
    return Equal(self, b ** e)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(x ** (a * OneMatrix(n)))

    i = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)



if __name__ == '__main__':
    run()
# created on 2021-12-19
