from util import *



@apply
def apply(given):
    fx, ou = given.of(Necessary)
    eqs = ou.of(Or)
    return tuple(Necessary(fx, eq) for eq in eqs)


@prove
def prove(Eq):
    from axiom import algebra
    x, b, a = Symbol(integer=True)
    f, g = Function(integer=True)


    Eq << apply(Necessary(f(x) > g(x), (a > b) | (f(a) > f(b))))

    Eq << algebra.necessary.necessary.imply.necessary.ou.apply(Eq[1], Eq[2])

if __name__ == '__main__':
    run()
