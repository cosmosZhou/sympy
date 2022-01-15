from util import *



@apply
def apply(given):
    fx, ou = given.of(Assuming)
    eqs = ou.of(Or)
    return tuple(Assuming(fx, eq) for eq in eqs)


@prove
def prove(Eq):
    from axiom import algebra
    x, b, a = Symbol(integer=True)
    f, g = Function(integer=True)


    Eq << apply(Assuming(f(x) > g(x), (a > b) | (f(a) > f(b))))

    Eq << algebra.assuming.assuming.imply.assuming.ou.apply(Eq[1], Eq[2])

if __name__ == '__main__':
    run()
# created on 2019-03-03
