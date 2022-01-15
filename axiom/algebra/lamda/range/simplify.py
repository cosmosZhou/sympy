from util import *


@apply
def apply(self, axis=0):
    expr, *limits = self.of(Lamda)
    
    i, domain = limits[axis]
    start, stop, step = domain.of(Range)
    limits[axis] = i, 0, Ceiling((stop - start) / step)
    expr = expr._subs(i, i * step + start)
    
    return Equal(self, Lamda(expr, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    d = Symbol(integer=True, positive=True)
    a, b, i = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(Lamda[i:Range(a, b, d)](f(i)))

    i = Symbol(domain=Range(Ceiling((b - a) / d)))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    
    


if __name__ == '__main__':
    run()
# created on 2021-12-27
# updated on 2021-12-27