from util import *


@apply
def apply(is_imply_P, is_imply_Q):
    p, q = is_imply_P.of(Infer)
    S[q], S[p] = is_imply_Q.of(Infer)
    return Equivalent(p, q)


@prove
def prove(Eq):
    p, q = Symbol(bool=True)
    Eq << apply(Infer(p, q), Infer(q, p))
    
    Eq <<= Eq[0] & Eq[1]


if __name__ == '__main__':
    run()
# created on 2022-01-27
