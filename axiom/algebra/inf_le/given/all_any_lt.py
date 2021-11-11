from util import *


@apply
def apply(given, M=None): 
    (fx, *limits), M0 = given.of(Inf <= Expr)
    variables = {x for x, *_ in limits}
    if M is None:
        M = given.generate_var(variables, real=True, var='M')
    elif isinstance(M, str):
        M = given.generate_var(variables, real=True, var=M)
        
    return All[M:Interval(M0, oo, left_open=True)](Any(fx < M, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    M0 = Symbol(real=True, given=True)
    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:a:b](f(x)) <= M0)

    Eq << algebra.all_any_lt.imply.le_inf.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-04-07
# updated on 2019-04-07
