from util import *


@apply
def apply(given, M=None): 
    (fx, *limits), M0 = given.of(Sup >= Expr)
    
    if M is None:
        M = given.generate_var(real=True, var='M')
    elif isinstance(M, str):
        M = given.generate_var(real=True, var=M)
        
    return All[M:Interval(-oo, M0, right_open=True)](Any(fx > M, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    M0 = Symbol(real=True, given=True)
    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:a:b](f(x)) >= M0)

    Eq << algebra.all_any_gt.imply.ge_sup.apply(Eq[1])


if __name__ == '__main__':
    run()