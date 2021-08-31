from util import *



@apply
def apply(imply):
    lhs, rhs = imply.of(Equal)
    assert lhs.is_nonzero or rhs.is_nonzero

    return Equal(log(lhs), log(rhs))

@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True)
    f, g = Function(shape=(), real=True, positive=True)

    Eq << apply(Equal(f(x), g(x)))

    Eq << Eq[1].apply(algebra.eq.imply.eq.exp)

if __name__ == '__main__':
    run()


