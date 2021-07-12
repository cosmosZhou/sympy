from util import *


@apply
def apply(self):
    from _collections import defaultdict
    # from sympy.utilities.iterables import topological_sort_depth_first
    # G = topological_sort_depth_first(graph)
    
    [[*args], *limits] = self.of(Sum[Mul])
        
    for i, b in enumerate(args):
        if b.is_Bool:
            break
    else:
        return
    
    del args[i]
    function = Mul(*args)
    
    cond = b.arg
    variables = self.variables_set
    if cond.is_And:
        eqs = {*cond.args}
        dic = defaultdict(set)
        for v in variables:
            otherVars = variables - {v}
            for eq in eqs:
                if eq._has(v) and not eq.has(*otherVars):
                    dic[v].add(eq)
            eqs -= dic[v]
            
        if eqs:
            for eq in eqs:
                for v, s in dic.items():
                    if not s and eq._has(v):
                        dic[v].add(eq)
                        break
                else:
                    return
        
        for v, cond in self.limits_dict.items():
            if not cond:
                continue
            if cond.is_set:
                cond = Contains(v, cond)
            dic[v].add(cond)
            
        graph = {x: set() for x in variables}
        for y, eqs in dic.items():
            if not eqs:
                continue

            free_symbols = set.union(*(eq.free_symbols for eq in eqs)) & (variables - {y})
            for x in free_symbols:
                # y is dependent on x, so x is a parent of y
                graph[x].add(y)

        from sympy.utilities.iterables import topological_sort_depth_first
        G = topological_sort_depth_first(graph)
        print(G)
        
        limits = []
        for v in G:
            eqs = dic[v]
            cond = And(*eqs)
            if cond.is_Contains and cond.lhs == v:
                cond = cond.rhs                
            limit = (v, cond)
            
            limits.append(limit)

    else:
        for i, v in enumerate(self.variables):
            if cond._has(v):
                [v] = limits[i]
                if cond.is_Contains and cond.lhs == v:
                    cond = cond.rhs
                limits[i] = (v, cond)
                break
            

    return Equal(self, Sum(function, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    A = Symbol.A(etype=dtype.integer)
    B = Function.B(etype=dtype.integer)
    C = Symbol.C(etype=dtype.integer)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    z = Symbol.z(integer=True)
    f = Function.f(real=True)
    Eq << apply(Sum[x, y, z:C](f(x, y) * Bool(Contains(x, A) & Contains(y, B(x)))))

    Eq << Eq[0].this.rhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.find(Bool).apply(algebra.bool.to.mul)

    Eq << Eq[-1].this.lhs.find(Bool[And]).apply(algebra.bool.to.mul)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.swap)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.swap, 1, 2)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.swap)


if __name__ == '__main__':
    run()