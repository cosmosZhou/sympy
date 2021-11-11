from util import *


# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    function, *limits = self.of(Cup)
    assert len(limits) == 2
    (i, *_ab), (j, *ab) = self.limits
    assert i.type == j.type
    z = Dummy('z', **i.type.dict)
    this = self.limits_subs(i, z)
    this = this.limits_subs(j, i)
    this = this.limits_subs(z, j)

    return Equal(self, this)


@prove
def prove(Eq):
    i, j, k = Symbol(integer=True)
    A = Symbol(etype=dtype.integer)
    n = Symbol(integer=True, positive=True)

    f = Function(integer=True)
    g = Symbol(shape=(oo, oo), etype=dtype.real)
    h = Symbol(shape=(oo,), etype=dtype.real)

    Eq << apply(Cup[i:f(j), j:A](h[i] & g[i, j]))


    Eq << Eq[-1].this.rhs.limits_subs(i, k)



if __name__ == '__main__':
    run()

# created on 2021-09-22
# updated on 2021-09-22
