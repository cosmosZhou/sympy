from util import *


@apply
def apply(eq_max, eq_min):
    (((i, l), (S[i - l], d)), limit_i), β = eq_max.of(Equal[Lamda[Max[Expr - Expr, Mod]]])
    ((iu1, n), S[limit_i]), ζ = eq_min.of(Equal[Lamda[Min]])
    u = iu1 - i - 1
    S[i], S[0], S[n] = limit_i

    return ζ[i] - β[i] <= Min(n, l + u + 1)



@prove
def prove(Eq):
    from axiom import algebra

    n, l, u, d = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    gram_width = l + u + 1 # in practice, gram_width = k_max * 2 + 1, where k_max = l = u
    start = i - l
    stop = start + gram_width  # i + k_max + 1
    β, ζ = Symbol(integer=True, shape=(n,))
    Eq << apply(Equal(β, Lamda[i:n](Max(start, start % d))), Equal(ζ, Lamda[i:n](Min(stop, n))))

    Eq << Eq[1] - Eq[0]

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.find(Max).apply(algebra.max.to.mul.min, -1)

    

    

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.min)

    Eq << Eq[-1].this.find(Min[~Add]).apply(algebra.add.to.min)

    Eq << Eq[-1].this.find(Min[~Add[Min]]).apply(algebra.add.to.min)

    Eq << LessEqual(Eq[-1].rhs, Eq[2].rhs, plausible=True)

    Eq << Eq[-1].subs(Eq[-2].reversed)

    
    


if __name__ == '__main__':
    run()
# created on 2021-12-26
# updated on 2021-12-26