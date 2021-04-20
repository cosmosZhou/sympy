from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra
from sympy.concrete.limits import limits_intersect


@apply
def apply(self, old, new):
    assert not old.is_given
    exists = self.limits_dict        
    if old in exists:
        domain = exists[old]
        eqs = []

        if not isinstance(domain, list):
            if not domain.is_set:
                domain = old.domain_conditioned(domain)
            if new.is_symbol:
                _eval_domain_defined = self.function.domain_defined(new)
                if _eval_domain_defined in domain:
                    ...
                else:
                    eqs.append(Contains(new, domain))
            else:
                eqs.append(Contains(new, domain))

        if self.function.is_And:
            for equation in self.function.args:
                eqs.append(equation.subs(old, new))
        else:
            eqs.append(self.function._subs(old, new))
        limits = self.limits_delete(old)
        if new.is_symbol and new.definition is None and not new.is_given:
            limits = limits_intersect(limits, [(new,)])

                    
        vars = {x for x, *_ in limits}
        limits += [(s,) for s in new.free_symbols if not s.is_given and s not in vars]
                    
        if limits:
            return self.func(And(*eqs), *limits)
        else: 
            return And(*eqs)
        
    if old.is_Slice:
        old = old.astype(Matrix)
        if old.is_DenseMatrix:
            old = Tuple(*old._mat)                    
            if old in exists or all(sym in exists for sym in old):
                ...
            else:
                return 

    if old.is_Tuple and all(sym in exists for sym in old): 
        domains = [exists[sym] for sym in old]
        eqs = []

        for domain in domains:
            if not isinstance(domain, list):
                if not domain.is_set:
                    domain = old.domain_conditioned(domain)                    
                eqs.append(Contains(new, domain))

        if self.function.is_And:
            for equation in self.function.args:
                eqs.append(equation._subs(old, new))
        else:
            if old.is_Tuple:
                function = self.function
                for i in range(len(old)):
                    function = function._subs(old[i], new[i])
                eqs.append(function)
            else:
                eqs.append(self.function._subs(old, new))
        limits = self.limits_delete(old)
        if new.is_symbol:
            limits = limits_intersect(limits, [(new,)])
        
        if limits:
            return self.func(And(*eqs), *limits)
        else:
            return And(*eqs)


@prove
def prove(Eq): 
    e = Symbol.e(real=True)
    x = Symbol.x(integer=True)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(Exists[x](x > g(x)), x, f(e))
    
    Eq << ~Eq[0]
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[-1].subs(x, f(e))
    
    Eq << ~Eq[-1]


if __name__ == '__main__':
    prove()

