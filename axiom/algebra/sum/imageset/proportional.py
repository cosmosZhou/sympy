from util import *


@apply
def apply(self):
    f, (m, domain) = self.of(Sum)
    n, expr, base_set = domain.image_set()
    
    assert not (expr / n)._has(n)
    f = f._subs(m, expr)

    return Equal(self, self.func(f, (n, base_set)))


@prove(proved=False)
def prove(Eq):
    n = Symbol.n(integer=True)
    f = Symbol.f(shape=(oo,), real=True)
    h = Function.h(real=True)
    t = Function.t(integer=True)
    a = Symbol.a(integer=True)
    Eq << apply(Sum[n:imageset(n, a * n, h(n) > 0)](f[n]))

    

    

    

    

    

    


if __name__ == '__main__':
    run()