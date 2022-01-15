from sympy.core.containers import Tuple
from sympy.sets.sets import Interval
from sympy.logic.boolalg import And


def limits_dict(limits):
    dic = {}
    for limit in limits:
        x, *domain = Tuple.as_setlimit(limit)
        if len(domain) == 1:
            dic[x] = domain[0]
        else:
            dic[x] = domain
    return dic

def limits_dictionary(limits):
    dic = {}
    for limit in limits:
        x, domain = limit.coerce_setlimit()        
        dic[x] = domain
    return dic

# perform topological_sort on limits
def limits_sort(limits_dict):
    G = {x: set() for x in limits_dict}

    for kinder in G:
        if not limits_dict[kinder]:
            continue

        for parent in limits_dict[kinder].free_symbols:
            if parent in G:
                G[parent].add(kinder)
                
    from sympy.utilities.iterables import topological_sort_depth_first, strongly_connected_components
    g = topological_sort_depth_first(G)

    if g is None:
        g = strongly_connected_components(G)
        for components in g:
            limit = And(*(limits_dict[v] for v in components)).latex
#             latex = r"\%s_{%s}{%s}" % (clause, limit, latex)

#         return latex
        return g

    limits = []
    for x in g:
        domain = limits_dict[x]
        if not domain:
            limit = (x,)
        elif domain.is_Range:
            limit = (x, domain.min(), domain.max() + 1)
        else:
            limit = (x, domain)
        limits.append(limit)

    return limits


# tests if limits include _limits
def limits_include(limits, _limits):
    dict_a = limits_dict(limits)
    dict_b = limits_dict(_limits)
    for var, domain in dict_b.items():
        if var not in dict_a or domain != dict_a[var]:
            return False
    return True


def limits_difference(limits, _limits):
    dict_b = limits_dict(_limits)
    newLimits = []
    for limit in limits: 
        if limit[0] in dict_b:
            continue
        newLimits.append(limit)    
    return newLimits


def limits_update(limits, *args):
    variables = [x for x, *_ in limits]

    if isinstance(limits, tuple):
        limits = [*limits]

    from sympy import Range
    def assign(old, domain):
        if isinstance(domain, (tuple, list)) and domain:
            new, *domain = domain
            if len(domain) == 1:
                domain = domain[0]
        else:
            new = old

        if isinstance(domain, Interval):
            if new.is_integer:
                domain = domain.copy(integer=True)
                if domain.is_Interval:
                    limit = (new, domain.start, domain.stop)
                else:
                    assert domain.is_FiniteSet
                    limit = (new, domain)
            else:
                if domain.left_open or domain.right_open:
                    limit = (new, domain)
                else:
                    limit = (new, domain.start, domain.stop)
        elif isinstance(domain, Range):
            if new.is_integer:
                limit = (new, domain.start, domain.stop)
            else:
                limit = (new, domain)
        
        elif isinstance(domain, (tuple, list)):
            limit = (new, *domain)
        else:
            limit = (new, domain)

        limits[variables.index(old)] = limit

    if len(args) == 1:
        dic = args[0]
        for args in dic.items():
            assign(*args)
    else:
        assign(*args)
    return limits


def limits_delete(limits, dic):
    variables = [x for x, *_ in limits]

    if isinstance(limits, tuple):
        limits = [*limits]

    if hasattr(dic, '__len__'):
        deletes = []
        for i, x in enumerate(variables):
            if x in dic:
                deletes.append(i)
        deletes.sort(reverse=True)

        for i in deletes:
            del limits[i]
    else:
        del limits[variables.index(dic)]
    return limits


def limits_common(limits, _limits, is_or=False, clue=None):
    self_dict = limits_dict(limits)
    eq_dict = limits_dict(_limits)
    keys = eq_dict.keys() & self_dict.keys()
    dic = {}
    if keys: 
        for x in keys:
            domain = self_dict[x]
            _domain = eq_dict[x]

            if isinstance(_domain, list):
                dic[x] = domain
                continue
            if _domain.is_set:
                if isinstance(domain, list):
                    if not domain:
                        domain = None
                    else:
                        domain = domain[0]
                    
                if domain is not None and not domain.is_set:
                    domain = x.domain_conditioned(domain)
            else:
                if domain.is_set:
                    _domain = x.domain_conditioned(_domain)

            if is_or:
                dic[x] = domain | _domain
            else:
                if domain != _domain:
                    if clue is not None:
                        clue['given'] = True
                if domain is None:
                    dic[x] = _domain
                else:
                    dic[x] = domain & _domain
        return dic
    for key in self_dict:
        if not key.is_Sliced:
            continue
        for _key in eq_dict:
            if not key._has(_key):
                continue
            dic[_key] = eq_dict[_key]
    return dic


def limits_intersect(limits, _limits, clue=None):
    dic = limits_common(limits, _limits, clue=clue)
    if dic:
        return limits_update(limits, dic) + limits_delete(_limits, dic)
    else:
        if type(_limits) != type(limits):
            _limits = type(limits)(_limits)
        return limits + _limits


def limits_empty(limits):
    for _, *ab in limits:
        if len(ab) != 1:
            return False
        domain, *_ = ab
        if not domain.is_EmptySet:
            return False
    return True


def limits_union(limits, _limits):
    dic = limits_common(limits, _limits, True)
    if dic:
        return limits_update(limits, dic) + limits_delete(_limits, dic)
    else:
        if type(_limits) != type(limits):
            _limits = type(limits)(_limits)
        return limits + _limits


def limits_cond(limits):
    eqs = []
    from sympy.sets.contains import Element
    limitsdict = limits_dict(limits)
    for x, cond in limitsdict.items():
        if isinstance(cond, list):
            if not cond:
                continue
            cond, baseset = cond
            cond &= Element(x, baseset)
        elif cond.is_set:
            cond = Element(x, cond)
        
        eqs.append(cond)
    return And(*eqs)
    
   
'''
fundamental theory of logic:
axiom:
1:
x & x = x
2:
x | x = x
3:
x & y = y & x
4:
x | y = y | x
5:
x & y | z = (x | z) & y | z
6:
x & (y | z) = x & y | x & z
7:
x & y => x
8:
if x => y, then y | x = y
9:
!(x & y) = !x | !y
10:
x = !!x

11:
Any[p] f = p & f
12:
All[p] f = !q | f
13:
x & !x = false  
14:
true = !false 

lemma:
1:
x => x | y
from x = x | x & y = (x | y) & x
2:
if x => y, then y & x = x

prove:

if x => y, then y | x = y

(y | x) & x = y & x
y & x | x = y & x
but x  = y & x | x
hence:
x = y & x

3:
!(Any[p] f) = All[p] !f
from definition
4:
!(All[p] f) = Any[p] !f
from definition
5:
Any[p] All[q] f => All[q] Any[p] f

prove:
Any[p] All[q] f = (!q | f) & p = = !q & p | f & p = (!q | f & p) & (p | f & p)
All[q] Any[p] f = !q | (f & p)
and 
(!q | f & p) & (p | f & p) => !q | (f & p)

6:
x => x
x = x & x => x

7:
!(x | y) = !x & !y
!!(x | y) = !(!x & !y)
!!(x | y) = !!x | !!y


8:
y = x & y | !x & y
prove:
x & y | !x & y = (x | !x) & y = true & y = y
'''
