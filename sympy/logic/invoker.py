

class Invoker:

    def __new__(cls, expr):
        this = object.__new__(cls)
        this._objs = []
        this._args = []
        this.index = []
        this._context = []
        this.append(expr)
        this.callable = None
        this._domain_defined = {}      
        return this
    
    @property
    def target(self):
        return self._objs[-1]
    
    @property
    def parent(self):
        return self._objs[-2]
    
    @property
    def source(self):
        return self._objs[0]

    def inference_status(self, boolean):
        for i in range(len(self.index)):
            boolean ^= self._objs[i].inference_status(self.index[i])
            
        return 'imply' if boolean else 'given'
        
    def determine_assumptions(self, obj):
        if obj.is_Inference and obj.is_Boolean: 
            equivalent = obj.equivalent
            if equivalent is not None:
                if not isinstance(equivalent, (list, tuple)):
                    # in case of result of simplify                    
                    if equivalent is not self.target:
                        clue = equivalent.clue
                        if clue is not None:
                            if clue == 'given':
                                return self.inference_status(False)
                            if clue == 'imply':
                                return self.inference_status(True)
                            return clue
            elif obj.given is not None: 
                return self.inference_status(False) 
            elif obj.imply is not None:
                return self.inference_status(True)
        return 'equivalent'
        
    def result(self, obj, simplify=True, evaluate=None):
        assumptions = {self.determine_assumptions(obj): self.source}

        for i in range(-1, -len(self.index) - 1, -1):
            this = self._objs[i - 1]
            args = [*this.args]
            args[self.index[i]] = obj
            
            stop = i == -len(self.index)
            
            if stop:
                kwargs = assumptions
            else:
                kwargs = this.kwargs
                
            if evaluate is not None:
                kwargs['evaluate'] = evaluate
            
            if self._domain_defined and this.func.is_ExprWithLimits:
                _, *limits = args
                for i, limit in enumerate(limits):
                    if limit[0] in self._domain_defined:
                        x, domain = limit.coerce_setlimit() 
                        domain_defined = self._domain_defined.pop(x)
                        if domain != domain_defined:
                            if domain_defined in domain: 
                                args[i + 1] = (x, domain_defined)
                                break
                else:
                    if this.is_All:
                        for x in set(self._domain_defined):
                            if this._has(x): 
                                args.append((x, self._domain_defined.pop(x)))                    

            obj = this.func(*args, **kwargs)
            
            if simplify and (not obj.is_All or stop or not self._objs[i - 2].is_Any):
                # exclude case Any[C](All[x](f(x) == C))
                obj = obj.simplify()
                
            if stop:
                break
        else:
            assert not len(self.index)
            obj = obj.copy(**assumptions)
             
        if obj.equivalent == self.source and obj == self.source:
            return self.source
        from sympy import Boolean
        if isinstance(self.source, Boolean):
            if 'given' in assumptions:
                from sympy import Suffice
                return Suffice(self.source, obj, plausible=None)
            if 'equivalent' in assumptions:
                from sympy import Equivalent
                return Equivalent(self.source, obj, plausible=None)
            
        return obj

    @property
    def this(self):
        return self.callable.__self__
        
    # simplify = True by default, use simplify = False in invoke, use simplify = None in simplification process after invoking!
    def __call__(self, *args, **kwargs):
        if self.callable is None:
            return self.enter(*args, **kwargs)
        
        this = self.this
        
        funcname = self.callable.__name__
        if funcname == 'subs':
            if not this.is_ConditionalBoolean:
                assert all(arg.is_Equal for arg in args)
                assert all(arg.plausible is None for arg in args)                
                args = map(lambda inf: inf.cond, args)
        
        if this.is_All: 
            if self.callable.__func__ is this.func.simplify:
                if self.parent.is_Any:
                    kwargs['local'] = True
                    
        evaluate = kwargs.pop('evaluate', None)
        obj = self.invoke(*args, **kwargs)
        
        return self.result(obj,
                           simplify=kwargs.get('simplify', True) is not None,
                           evaluate=evaluate)

    def invoke(self, *args, **kwargs):
        if self._context:
            this = self.this
            reps = []
            from sympy import Interval, Range
            outer_context = {}
            for _, limits in self._context:
                for x, *ab in limits:
                    if x.shape:
                        continue
                    if len(ab) == 1:
                        domain, *_ = ab
                        if domain.is_Boolean:
                            domain = x.domain_conditioned(domain)                                                    
                    else:
                        for i, t in enumerate(ab):
                            for outer_var in outer_context:
                                if t._has(outer_var):
                                    t = t._subs(outer_var, outer_context[outer_var][0])
                            ab[i] = t
                                
                        domain = (Range if x.is_integer else Interval)(*ab)
                        
                    if x in outer_context:
                        x, _domain = outer_context[x]
                        keys = domain.free_symbols & outer_context.keys()
                        if keys:
                            for key in keys:
                                domain = domain._subs(key, outer_context[key][0])
                        domain &= _domain
                            
                    _x = x.copy(domain=domain)
                    this = this._subs(x, _x).simplify()
                    reps.append((x, _x))
                    outer_context[x] = (_x, domain)
            
            obj = getattr(this, self.callable.__name__)(*args, **kwargs)
            if obj.is_BooleanAtom:
                if obj.is_BooleanTrue:
                    parent = self.parent
                    if parent.is_ExprCondPair:
                        if self.target is parent.cond:
                            return self.target
                return obj                
            
            reps.reverse()
            for x, _x in reps:
                _obj = obj._subs(_x, x)
                if obj.is_boolean:
                    if _obj.is_BooleanAtom:
                        _obj = _obj.copy(equivalent=obj)
                obj = _obj                    
        else: 
            obj = self.callable(*args, **kwargs)
        return obj
        
    def append(self, obj):
        self._objs.append(obj)

    def fetch_from_path(self, *path, struct=None):
        target = self.target
        if struct is not None: 
            target.fetch_from_path(*path, struct=struct)            
            
        for index in path:
            self.index.append(index)
            target = target.args[index]
            self.append(target)
            
        return self
        
    def target_from_path(self, target, *path):
        for index in path:
            target = target.args[index]
        return target
    
    def find(self, *query): 
        from sympy import Basic        
        query, struct = Basic.make_query(*query)
        
        return self.target.yield_one([(q, []) for q in query],
                                   foreach=Basic.find_path,
                                   func=self.target_from_path,
                                   fetch=self.fetch_from_path,
                                   output=[],
                                   struct=struct)                      
                                    
    method2index = {'rhs': 1,
                    'lhs': 0,
                    'function': 0,
                    'arg': 0,
                    'cond': 1,
                    'expr': 0,
                    'base': 0}

    def __getattr__(self, method): 
        target = self.target
        if method == 'T':
            if len(target.shape) > 1:
                return self
            
        obj = getattr(target, method)
        
        if method == 'definition':
            # beware that application of definition may cause the domain definition to be altered, thus causing logic error!
            target_keys = target._domain_defined.keys()
            obj_keys = obj._domain_defined.keys()
            for key in target_keys & obj_keys:
                original_domain = target.domain_defined(key)
                altered_domain = obj.domain_defined(key)
                if original_domain != altered_domain:
                    
                    if original_domain not in altered_domain:
                        from sympy.core.function import AppliedUndef
                        assert target._has(AppliedUndef)
#                             print(original_domain)
#                             print(altered_domain)
                        assert altered_domain in original_domain
                        target._domain_defined[key] = altered_domain
                        original_domain = altered_domain
                        
                    assert original_domain in altered_domain, "original domain of definition must lie in transformed domain of definition!"                    
                    assert key not in self._domain_defined                    
                    self._domain_defined[key] = original_domain
            
        if callable(obj):
            self.callable = obj
            return self

        if isinstance(obj, tuple):
            self.append(obj)
            return self
        
        index = self.method2index.get(method)
        if index is None:
            return self.result(obj)
            
        self.index.append(index)
        self.append(obj)

        return self

    def __neg__(self):
        if self.target.is_Relational:
            self.callable = self.target.__neg__
            return self.__call__()

    def __sub__(self, rhs):
        if self.target.is_Relational:
            self.callable = self.target.__sub__
            return self.__call__(rhs)
        
    def __add__(self, rhs):
        if self.target.is_Relational:
            self.callable = self.target.__add__
            return self.__call__(rhs)
        
    def __truediv__(self, rhs):
        if self.target.is_Relational:
            self.callable = self.target.__truediv__
            return self.__call__(rhs)

    def __mul__(self, rhs):
        if self.target.is_Relational:
            self.callable = self.target.__mul__
            return self.__call__(rhs)

    def __mod__(self, rhs):
        if self.target.is_Equal:
            self.callable = self.target.__mod__
            return self.__call__(rhs)
        
    def __matmul__(self, rhs):
        if self.target.is_Equal:
            self.callable = self.target.__matmul__
            return self.__call__(rhs)

    def __str__(self):
        return str(self.target)

    @property
    def latex(self):
        return self.value.latex

    def _pretty(self, p):
        return p._print(self.target)

    def __getitem__(self, indices):
        target = self.target
        
        if isinstance(target, tuple):
            obj = target[indices]
            self.index.append(self.parent.args.index(obj))
            self._objs[-1] = obj
        elif target.is_Tuple:
            self.index.append(indices)
            self._objs.append(target[indices])
        elif target.is_Matrix:
            if isinstance(indices, tuple):
                i, j = indices
                index = i * target.cols + j
            else:
                index = indices
            
            self.index.append(index)
            self._objs.append(target.args[index])
        else:
            self = self.result(target[indices]) 
                        
        return self

    def __iter__(self):
        return iter(self.obj)

    def enter(self, *args, **kwargs):
        target = self.target
        limits = ()
        
        if target.is_ExprWithLimits: 
            if not args and not kwargs:
                limits = []
                for limit in target.limits:
                    x, *ab = limit
                    if not ab and x.is_integer:
                        limit = (x, target.function.domain_defined(x))
                    limits.append(limit)
                limits.reverse()      
            else:
                limits = target.limits
            
        elif target.is_ExprCondPair:
            piecewise = self.parent
            cond = target.cond
            for e, c in piecewise.args:
                if e == target.expr:
                    break
                cond &= c.invert()
                
            if cond.is_And:
                limits = tuple((eq.wrt, eq) for eq in cond.args)
            else: 
                limits = ((cond.wrt, cond),)
        if args:
            limits += tuple((x, target.domain_defined(x)) for x in args)
        if kwargs: 
            if 'shape' in kwargs:
                shape = kwargs['shape']
                limits = tuple(limit for limit in limits if limit[0].shape == shape)
            elif 'var' in kwargs:
                var = kwargs['var']
                limits = tuple(limit for limit in limits if limit[0] == var)                
                          
        self._context.append((target, limits))
        return self

    def __or__(self, x):
        if self.assumptions is None:
            self.assumptions = []
        target = self.target
        domain = target.domain_defined(x)
        self.assumptions.append((x, domain))
        return self


class Identity(Invoker):

    def result(self, obj): 
        from sympy import Equal
        
        for i in range(-1, -len(self.index) - 1, -1):
            this = self._objs[i - 1]
            args = [*this.args]
            args[self.index[i]] = obj
            obj = this.func(*args).simplify()            

        return Equal(self.source, obj, evaluate=False, plausible=None)            
        
    def __call__(self, *args, **kwargs):
        if self.callable is None:
            return self.enter(*args)
        
        if self.callable.__name__ == 'subs':
            this = self.this
            if this.is_AddWithLimits:
                if len(args) == 2:
                    (x, *_), *_ = this.limits
                    # domain might be different!
                    assert args[0].name == x.name
#             elif self.obj.__self__.is_ConditionalBoolean:
#                 ...
            else: 
                assert all(arg.is_Equal and arg.plausible is None for arg in args)                
                args = map(lambda inf: inf.cond, args)

        obj = self.invoke(*args, **kwargs)
        
        return self.result(obj)

