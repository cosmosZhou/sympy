from util import *


@apply
def apply(eq1, eq2, f_eq): 
    if not eq1.is_Equal:
        f_eq, eq1 = eq1, f_eq
        
    old, new = eq1.of(Equal)
    f_eq = f_eq._subs(old, new)
    old, new = eq2.of(Equal)
    f_eq = f_eq._subs(old, new)
    return f_eq


@prove
def prove(Eq):
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True, shape=(m, n))
    b = Symbol.b(real=True, shape=(m, n))
    c = Symbol.c(real=True, shape=(m, n))
    d = Symbol.d(real=True, shape=(m, n))
    S = Symbol.S(etype=dtype.real * (m, n))
    Eq << apply(Equal(a, 2 * c), Equal(b, 2 * d), Contains(a * b, S))

    Eq << Eq[2].subs(Eq[0])
    Eq << Eq[-1].subs(Eq[1])
    


if __name__ == '__main__':
    run()