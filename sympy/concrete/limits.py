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


def limits_update(limits, *args):
    variables = [x for x, *_ in limits]

    if isinstance(limits, tuple):
        limits = [*limits]

    def assign(old, domain):
        if isinstance(domain, (tuple, list)) and domain:
            new, *domain = domain
            if len(domain) == 1:
                domain = domain[0]
        else:
            new = old

        if isinstance(domain, Interval) and (not new.is_integer) == (not domain.is_integer):
            limit = (new, domain.min(), domain.max() + 1)
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
                    domain = domain[0]
                    
                if not domain.is_set:
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
                dic[x] = domain & _domain
        return dic
    for key in self_dict:
        if not key.is_Slice:
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

def limits_complement(limits, _limits):
    new_limits = []
    for limit, _limit in zip(limits, _limits):
        if len(limit) == len(_limit) == 3:
            x, a, b = limit
            _x, _a, _b = _limit
            if x == _x:
                if a == _a:
                    if _b <= b:
                        new_limits.append((x, _b, b))
                    else:
                        return
                else:
                    return
            else:
                return
        else:
            return 
    return new_limits

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


# perform topological_sort on limits
def limits_sort(limits):
    forall = limits_dict(limits)
    G = {x: set() for x, *_ in limits}

    for kinder in G:
        if forall[kinder] is None:
            continue

        for parent in forall[kinder].free_symbols:
            if parent in G:
                G[parent].add(kinder)
    from sympy.utilities.iterables import topological_sort_depth_first, strongly_connected_components
    g = topological_sort_depth_first(G)

    if g is None:
        g = strongly_connected_components(G)
        for components in g:
            limit = And(*(forall[v] for v in components)).latex
            latex = r"\%s_{%s}{%s}" % (clause, limit, latex)

        return latex

    limits = []
    for x in g:
        domain = forall[x]
        if domain.is_Interval and domain.is_integer:
            limit = (x, domain.min(), domain.max() + 1)
        else:
            limit = (x, domain)
        limits.append(limit)

    return limits



def limits_condition(limits):
    eqs = []
    from sympy.sets.contains import Contains
    limitsdict = limits_dict(limits)
    for x, cond in limitsdict.items():
        if isinstance(cond, list):
            if not cond:
                continue
            cond, baseset = cond
            cond &= Contains(x, baseset)
        elif cond.is_set:
            cond = Contains(x, cond)
        
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
Exists[p] f = p & f
12:
ForAll[p] f = !q | f
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
!(Exists[p] f) = ForAll[p] !f
from definition
4:
!(ForAll[p] f) = Exists[p] !f
from definition
5:
Exists[p] ForAll[q] f => ForAll[q] Exists[p] f

prove:
Exists[p] ForAll[q] f = (!q | f) & p = = !q & p | f & p = (!q | f & p) & (p | f & p)
ForAll[q] Exists[p] f = !q | (f & p)
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
