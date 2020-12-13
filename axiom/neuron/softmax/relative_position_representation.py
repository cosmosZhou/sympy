
from axiom.utility import plausible
from sympy.core.relational import Equality
from sympy.functions.elementary.exponential import softmax
from sympy import Symbol
from sympy.functions.elementary.miscellaneous import sqrt, Min, Max
from sympy.matrices.expressions.matmul import MatMul
from sympy.concrete.summations import Sum
from sympy import LAMBDA
from sympy.core.function import Function
from sympy.sets.contains import Contains
from sympy.sets.sets import Interval
from sympy.core.add import Plus

clip = Function.clip(nargs=(3,), shape=(), eval=lambda a, a_min, a_max: Min(a_max, Max(a, a_min)))

@plausible
def apply(n, dx, dz):
    x = Symbol.x(shape=(n, dx), real=True)
    W_Q = Symbol("W^Q", shape=(dx, dz), real=True)
    W_K = Symbol("W^K", shape=(dx, dz), real=True)
    W_V = Symbol("W^V", shape=(dx, dz), real=True)
    
    Q = Symbol.Q(definition=x @ W_Q)
    K = Symbol.K(definition=x @ W_K)
    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    
    k = Symbol.k(integer=True, positive=True)
    w_K = Symbol("w^K", shape=(2 * k + 1, dz), real=True)
    w_V = Symbol("w^V", shape=(2 * k + 1, dz), real=True)
    
    a_K = Symbol("a^K", definition=LAMBDA[j:n, i:n](w_K[k + clip(j - i, -k, k)]))
    a_V = Symbol("a^V", definition=LAMBDA[j:n, i:n](w_V[k + clip(j - i, -k, k)]))
    
    e = Symbol.e(definition=Q @ (K + a_K).T / sqrt(dz))
    α = Symbol.α(definition=softmax(e))
    
    z = Symbol.z(definition=α @ (x @ W_V + a_V))
    
    return Contains(k + clip(j - i, -k, k), Interval(0, 2 * k, integer=True)), Equality(z[i], Sum[j:n](α[i, j] * (x[j] @ W_V + a_V[i, j]))), Equality(e[i, j], (x[i] @ W_Q @ (x[j] @ W_K + a_K[i, j])) / sqrt(dz))


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True)
    dx = Symbol.d_x(integer=True, positive=True)
    dz = Symbol.d_z(integer=True, positive=True)

    Eq << apply(n, dx, dz)
    i, j = Eq[2].lhs.indices
    Eq << Eq[-1].subs(Eq[0][i].reversed)
    
    Eq << Eq[-1].subs(Eq[1][j].reversed)
    

    
    Eq << Eq[3][i, j]
    
    Eq << Eq[4][i, j]
    
    Eq << Eq[6][i]
    
    V = Symbol.V(definition=MatMul(*Eq[-1].rhs.args[1].args[1:]))
    Eq.V_definition = V.this.definition
    
    Eq << Eq[-1].this.rhs.subs(Eq.V_definition.reversed)

    Eq << Eq[-1].this.rhs.astype(Plus)
        
    k = Symbol.k(integer=True)
    Eq << Eq[-1].this.rhs.args[0].expand(free_symbol={k})
    
    Eq << Eq[-1].this.rhs.args[-1].astype(Sum)
    
    Eq << Eq[-1].this.rhs.subs(Eq.V_definition[j])
    
    Eq << Eq[-1].this.rhs.args[0].expand(free_symbol={k})
    
    Eq << Eq[-1].this.rhs.args[0].astype(Sum)
    
    Eq << Eq[-1].this.rhs.astype(Sum)
    
    α = Eq[4].lhs
    Eq << Eq[-1].this.rhs.function.collect(α[i, j])
    
    Eq << Eq[7].this.lhs.args[1].definition

    Eq << Eq[-1].this.lhs.astype(Min)


if __name__ == '__main__':
    prove(__file__)
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
