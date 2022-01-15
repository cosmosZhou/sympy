from util import *


@apply
def apply(self):
    axis = self.axis
    f, *limits = self.of(Transpose[axis][Lamda])
    variables = {var for var, *ab in limits}
    j = self.generate_var(variables, integer=True)
    
    assert axis >= len(limits)
    if axis == self.default_axis:
        [(i, S[0], m)] = limits
        [n] = f.shape
        rhs = Lamda[i:m, j:n](f[j]).simplify()
    else:
        index = -axis - 1
        
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i, j, k = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    d = Symbol(integer=True, shape=(oo,))
    h = Symbol(real=True, shape=(oo, n, n))
    Eq << apply(Lamda[i:m](h[j, d[i]]).T)

    i = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    


if __name__ == '__main__':
    run()
# created on 2022-01-11
