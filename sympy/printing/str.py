"""
A Printer for generating readable representation of most sympy classes.
"""
from sympy.core import S, Rational, Pow, Basic, Mul
from sympy.core.mul import _keep_coeff

from .printer import Printer
from sympy.printing.precedence import precedence, PRECEDENCE

from mpmath.libmp import prec_to_dps, to_str as mlib_to_str

from sympy.utilities import default_sort_key


class StrPrinter(Printer):
    printmethod = "_sympystr"
    _default_settings = {
        "order": None,
        "full_prec": "auto",
        "sympy_integers": False,
        "abbrev": False,
    }

    _relationals = dict()

    def parenthesize(self, item, level, strict=False):
        if (precedence(item) < level) or ((not strict) and precedence(item) <= level):
            return "(%s)" % self._print(item)
        else:
            return self._print(item)

    def stringify(self, args, sep, level=0):
        return sep.join([self.parenthesize(item, level) for item in args])

    def emptyPrinter(self, expr):
        if isinstance(expr, str):
            return expr
        elif isinstance(expr, Basic):
            return repr(expr)
        else:
            return str(expr)

    def _print_BooleanTrue(self, expr):
        return "True"

    def _print_BooleanFalse(self, expr):
        return "False"

    def _print_Not(self, expr):
        return '~%s' % (self.parenthesize(expr.args[0], PRECEDENCE["Not"]))

    def _print_AppliedPredicate(self, expr):
        return '%s(%s)' % (self._print(expr.func), self._print(expr.arg))

    def _print_Basic(self, expr):
        l = [self._print(o) for o in expr.args]
        return expr.__class__.__name__ + "(%s)" % ", ".join(l)

    def _print_BlockMatrix(self, B):
        if B.blocks.shape == (1, 1):
            self._print(B.blocks[0, 0])
        return self._print(B.blocks)

    def _print_Catalan(self, expr):
        return 'Catalan'

    def _print_ComplexInfinity(self, expr):
        return 'zoo'

    def _print_ConditionSet(self, s):
        args = tuple([self._print(i) for i in (s.variable, s.condition)])
        if s.base_set.is_UniversalSet:
            return 'ConditionSet(%s, %s)' % args
        args += (self._print(s.base_set),)
        return 'ConditionSet(%s, %s, %s)' % args

    def _print_dict(self, d):
        keys = sorted(d.keys(), key=default_sort_key)
        items = []

        for key in keys:
            item = "%s: %s" % (self._print(key), self._print(d[key]))
            items.append(item)

        return "{%s}" % ", ".join(items)

    def _print_Dict(self, expr):
        return self._print_dict(expr)

    def _print_RandomDomain(self, d):
        if hasattr(d, 'as_boolean'):
            return 'Domain: ' + self._print(d.as_boolean())
        elif hasattr(d, 'set'):
            return ('Domain: ' + self._print(d.symbols) + ' in ' + 
                    self._print(d.set))
        else:
            return 'Domain on ' + self._print(d.symbols)

    def _print_Dummy(self, expr):
        return '_' + expr.name

    def _print_EulerGamma(self, expr):
        return 'EulerGamma'

    def _print_Exp1(self, expr):
        return 'E'

    def _print_ExprCondPair(self, expr):
        return '(%s, %s)' % (self._print(expr.expr), self._print(expr.cond))

    def _print_FiniteSet(self, s):
        s = sorted(s, key=default_sort_key)
        if len(s) > 10:
            printset = s[:3] + ['...'] + s[-3:]
        else:
            printset = s
        return '{' + ', '.join(self._print(el) for el in printset) + '}'

    def _print_GeometryEntity(self, expr):
        # GeometryEntity is special -- it's base is tuple
        return str(expr)

    def _print_GoldenRatio(self, expr):
        return 'GoldenRatio'

    def _print_TribonacciConstant(self, expr):
        return 'TribonacciConstant'

    def _print_ImaginaryUnit(self, expr):
        return 'I'

    def _print_Infinity(self, expr):
        return 'oo'

    def _print_Infinitesimal(self, expr):
        return "epsilon"

    def _print_AccumulationBounds(self, i):
        return "AccumBounds(%s, %s)" % (self._print(i.min),
                                        self._print(i.max))

    def _print_Inverse(self, I):
        return "%s**(-1)" % self.parenthesize(I.arg, PRECEDENCE["Pow"])

    def _print_LatticeOp(self, expr):
        args = sorted(expr.args, key=default_sort_key)
        return expr.func.__name__ + "(%s)" % ", ".join(self._print(arg) for arg in args)

    def _print_list(self, expr):
        return "[%s]" % self.stringify(expr, ", ")

    def _print_MatrixBase(self, expr):
        return expr._format_str(self)

    _print_MutableSparseMatrix = \
        _print_ImmutableSparseMatrix = \
        _print_Matrix = \
        _print_DenseMatrix = \
        _print_MutableDenseMatrix = \
        _print_ImmutableMatrix = \
        _print_ImmutableDenseMatrix = \
        _print_MatrixBase

    def _print_MatrixElement(self, expr):
        if len(expr.args) == 3:
            return self.parenthesize(expr.parent, PRECEDENCE["Atom"], strict=True) \
                +'[%s, %s]' % (self._print(expr.i), self._print(expr.j))
        else:
            return self.parenthesize(expr.parent, PRECEDENCE["Atom"], strict=True) + '[%s]' % self._print(expr.i)


    def _print_MatrixSlice(self, expr):

        def strslice(x):
            x = list(x)
            if x[2] == 1:
                del x[2]
            if x[1] == x[0] + 1:
                del x[1]
            if x[0] == 0:
                x[0] = ''
            return ':'.join(map(lambda arg: self._print(arg), x))

        return (self._print(expr.parent) + '[' + 
                strslice(expr.rowslice) + ', ' + 
                strslice(expr.colslice) + ']')

    def _print_DeferredVector(self, expr):
        return expr.name

    def _print_HadamardProduct(self, expr):
        return '.*'.join([self.parenthesize(arg, precedence(expr)) for arg in expr.args])

    def _print_HadamardPower(self, expr):
        PREC = precedence(expr)
        return '.**'.join([
            self.parenthesize(expr.base, PREC),
            self.parenthesize(expr.exp, PREC)
        ])

    def _print_ElementwiseApplyFunction(self, expr):
        return "{0}({1}...)".format(
            expr.function,
            self._print(expr.expr),
        )

    def _print_NaN(self, expr):
        return 'nan'

    def _print_NegativeInfinity(self, expr):
        return '-oo'

    def _print_NegativeInfinitesimal(self, expr):
        return "-epsilon"

    def _print_Order(self, expr):
        if not expr.variables or all(p is S.Zero for p in expr.point):
            if len(expr.variables) <= 1:
                return 'O(%s)' % self._print(expr.expr)
            else:
                return 'O(%s)' % self.stringify((expr.expr,) + expr.variables, ', ', 0)
        else:
            return 'O(%s)' % self.stringify(expr.args, ', ', 0)

    def _print_Ordinal(self, expr):
        return expr.__str__()

    def _print_Cycle(self, expr):
        return expr.__str__()

    def _print_Permutation(self, expr):
        from sympy.combinatorics.permutations import Permutation, Cycle
        if Permutation.print_cyclic:
            if not expr.size:
                return '()'
            # before taking Cycle notation, see if the last element is
            # a singleton and move it to the head of the string
            s = Cycle(expr)(expr.size - 1).__repr__()[len('Cycle'):]
            last = s.rfind('(')
            if not last == 0 and ',' not in s[last:]:
                s = s[last:] + s[:last]
            s = s.replace(',', '')
            return s
        else:
            s = expr.support()
            if not s:
                if expr.size < 5:
                    return 'Permutation(%s)' % self._print(expr.array_form)
                return 'Permutation([], size=%s)' % self._print(expr.size)
            trim = self._print(expr.array_form[:s[-1] + 1]) + ', size=%s' % self._print(expr.size)
            use = full = self._print(expr.array_form)
            if len(trim) < len(full):
                use = trim
            return 'Permutation(%s)' % use

    def _print_Subs(self, obj):
        expr, old, new = obj.args
        if len(obj.point) == 1:
            old = old[0]
            new = new[0]
        return "Subs(%s, %s, %s)" % (
            self._print(expr), self._print(old), self._print(new))

    def _print_TensorIndex(self, expr):
        return expr._print()

    def _print_TensorHead(self, expr):
        return expr._print()

    def _print_Tensor(self, expr):
        return expr._print()

    def _print_TensMul(self, expr):
        # prints expressions like "A(a)", "3*A(a)", "(1+x)*A(a)"
        sign, args = expr._get_args_for_traditional_printer()
        return sign + "*".join(
            [self.parenthesize(arg, precedence(expr)) for arg in args]
        )

    def _print_TensAdd(self, expr):
        return expr._print()

    def _print_PermutationGroup(self, expr):
        p = ['    %s' % self._print(a) for a in expr.args]
        return 'PermutationGroup([\n%s])' % ',\n'.join(p)

    def _print_PolyRing(self, ring):
        return "Polynomial ring in %s over %s with %s order" % \
            (", ".join(map(lambda rs: self._print(rs), ring.symbols)),
            self._print(ring.domain), self._print(ring.order))

    def _print_FracField(self, field):
        return "Rational function field in %s over %s with %s order" % \
            (", ".join(map(lambda fs: self._print(fs), field.symbols)),
            self._print(field.domain), self._print(field.order))

    def _print_FreeGroupElement(self, elm):
        return elm.__str__()

    def _print_PolyElement(self, poly):
        return poly.str(self, PRECEDENCE, "%s**%s", "*")

    def _print_FracElement(self, frac):
        if frac.denom == 1:
            return self._print(frac.numer)
        else:
            numer = self.parenthesize(frac.numer, PRECEDENCE["Mul"], strict=True)
            denom = self.parenthesize(frac.denom, PRECEDENCE["Atom"], strict=True)
            return numer + "/" + denom

    def _print_Poly(self, expr):
        ATOM_PREC = PRECEDENCE["Atom"] - 1
        terms, gens = [], [ self.parenthesize(s, ATOM_PREC) for s in expr.gens ]

        for monom, coeff in expr.terms():
            s_monom = []

            for i, exp in enumerate(monom):
                if exp > 0:
                    if exp == 1:
                        s_monom.append(gens[i])
                    else:
                        s_monom.append(gens[i] + "**%d" % exp)

            s_monom = "*".join(s_monom)

            if coeff.is_Add:
                if s_monom:
                    s_coeff = "(" + self._print(coeff) + ")"
                else:
                    s_coeff = self._print(coeff)
            else:
                if s_monom:
                    if coeff is S.One:
                        terms.extend(['+', s_monom])
                        continue

                    if coeff is S.NegativeOne:
                        terms.extend(['-', s_monom])
                        continue

                s_coeff = self._print(coeff)

            if not s_monom:
                s_term = s_coeff
            else:
                s_term = s_coeff + "*" + s_monom

            if s_term.startswith('-'):
                terms.extend(['-', s_term[1:]])
            else:
                terms.extend(['+', s_term])

        if terms[0] in ['-', '+']:
            modifier = terms.pop(0)

            if modifier == '-':
                terms[0] = '-' + terms[0]

        format = expr.__class__.__name__ + "(%s, %s"

        from sympy.polys.polyerrors import PolynomialError

        try:
            format += ", modulus=%s" % expr.get_modulus()
        except PolynomialError:
            format += ", domain='%s'" % expr.get_domain()

        format += ")"

        for index, item in enumerate(gens):
            if len(item) > 2 and (item[:1] == "(" and item[len(item) - 1:] == ")"):
                gens[index] = item[1:len(item) - 1]

        return format % (' '.join(terms), ', '.join(gens))

    def _print_ProductSet(self, p):
        return ' x '.join(self._print(s) for s in p.sets)

    def _print_UniversalSet(self, p):
        return 'UniversalSet'

    def _print_AlgebraicNumber(self, expr):
        if expr.is_aliased:
            return self._print(expr.as_poly().as_expr())
        else:
            return self._print(expr.as_expr())

    def _print_UnevaluatedExpr(self, expr):
        return self._print(expr.args[0])

    def _print_ImmutableDenseNDimArray(self, expr):
        return str(expr)

    def _print_ImmutableSparseNDimArray(self, expr):
        return str(expr)

    def _print_Integer(self, expr):
        if self._settings.get("sympy_integers", False):
            return "S(%s)" % (expr)
        return str(expr.p)

    def _print_Integers(self, expr):
        return 'Integers'

    def _print_Naturals(self, expr):
        return 'Naturals'

    def _print_Naturals0(self, expr):
        return 'Naturals0'

    def _print_Reals(self, expr):
        return 'Reals'

    def _print_int(self, expr):
        return str(expr)

    def _print_mpz(self, expr):
        return str(expr)

    def _print_Rational(self, expr):
        if expr.q == 1:
            return str(expr.p)
        else:
            if self._settings.get("sympy_integers", False):
                return "S(%s)/%s" % (expr.p, expr.q)
            return "%s/%s" % (expr.p, expr.q)

    def _print_PythonRational(self, expr):
        if expr.q == 1:
            return str(expr.p)
        else:
            return "%d/%d" % (expr.p, expr.q)

    def _print_Fraction(self, expr):
        if expr.denominator == 1:
            return str(expr.numerator)
        else:
            return "%s/%s" % (expr.numerator, expr.denominator)

    def _print_mpq(self, expr):
        if expr.denominator == 1:
            return str(expr.numerator)
        else:
            return "%s/%s" % (expr.numerator, expr.denominator)

    def _print_Float(self, expr):
        prec = expr._prec
        if prec < 5:
            dps = 0
        else:
            dps = prec_to_dps(expr._prec)
        if self._settings["full_prec"] is True:
            strip = False
        elif self._settings["full_prec"] is False:
            strip = True
        elif self._settings["full_prec"] == "auto":
            strip = self._print_level > 1
        rv = mlib_to_str(expr._mpf_, dps, strip_zeros=strip)
        if rv.startswith('-.0'):
            rv = '-0.' + rv[3:]
        elif rv.startswith('.0'):
            rv = '0.' + rv[2:]
        if rv.startswith('+'):
            # e.g., +inf -> inf
            rv = rv[1:]
        return rv

    def _print_ComplexRootOf(self, expr):
        return "CRootOf(%s, %d)" % (self._print_Add(expr.expr, order='lex'),
                                    expr.index)

    def _print_RootSum(self, expr):
        args = [self._print_Add(expr.expr, order='lex')]

        if expr.fun is not S.IdentityFunction:
            args.append(self._print(expr.fun))

        return "RootSum(%s)" % ", ".join(args)

    def _print_GroebnerBasis(self, basis):
        cls = basis.__class__.__name__

        exprs = [self._print_Add(arg, order=basis.order) for arg in basis.exprs]
        exprs = "[%s]" % ", ".join(exprs)

        gens = [ self._print(gen) for gen in basis.gens ]
        domain = "domain='%s'" % self._print(basis.domain)
        order = "order='%s'" % self._print(basis.order)

        args = [exprs] + gens + [domain, order]

        return "%s(%s)" % (cls, ", ".join(args))

    def _print_set(self, s):
        items = sorted(s, key=default_sort_key)

        args = ', '.join(self._print(item) for item in items)
        if not args:
            return "set()"
        return '{%s}' % args

    def _print_frozenset(self, s):
        if not s:
            return "frozenset()"
        return "frozenset(%s)" % self._print_set(s)

    def _print_SparseMatrix(self, expr):
        from sympy.matrices import Matrix
        return self._print(Matrix(expr))
    
    def _print_OneMatrix(self, expr):
        return "1"

    def _print_Predicate(self, expr):
        return "Q.%s" % expr.name

    def _print_str(self, expr):
        return str(expr)

    def _print_tuple(self, expr):
        if len(expr) == 1:
            return "(%s,)" % self._print(expr[0])
        else:
            return "(%s)" % self.stringify(expr, ", ")

    def _print_Tuple(self, expr):
        return self._print_tuple(expr)

    def _print_Uniform(self, expr):
        return "Uniform(%s, %s)" % (self._print(expr.a), self._print(expr.b))

    def _print_Complement(self, expr):
        return r' \ '.join(self._print(set_) for set_ in expr.args)

    def _print_Quantity(self, expr):
        if self._settings.get("abbrev", False):
            return "%s" % expr.abbrev
        return "%s" % expr.name

    def _print_Quaternion(self, expr):
        s = [self.parenthesize(i, PRECEDENCE["Mul"], strict=True) for i in expr.args]
        a = [s[0]] + [i + "*" + j for i, j in zip(s[1:], "ijk")]
        return " + ".join(a)

    def _print_Dimension(self, expr):
        return str(expr)

    def _print_Wild(self, expr):
        return expr.name + '_'

    def _print_WildFunction(self, expr):
        return expr.name + '_'

    def _print_Zero(self, expr):
        if self._settings.get("sympy_integers", False):
            return "S(0)"
        return "0"

    def _print_DMP(self, p):
        from sympy.core.sympify import SympifyError
        try:
            if p.ring is not None:
                # TODO incorporate order
                return self._print(p.ring.to_sympy(p))
        except SympifyError:
            pass

        cls = p.__class__.__name__
        rep = self._print(p.rep)
        dom = self._print(p.dom)
        ring = self._print(p.ring)

        return "%s(%s, %s, %s)" % (cls, rep, dom, ring)

    def _print_DMF(self, expr):
        return self._print_DMP(expr)

    def _print_Object(self, obj):
        return 'Object("%s")' % obj.name

    def _print_IdentityMorphism(self, morphism):
        return 'IdentityMorphism(%s)' % morphism.domain

    def _print_NamedMorphism(self, morphism):
        return 'NamedMorphism(%s, %s, "%s")' % \
               (morphism.domain, morphism.codomain, morphism.name)

    def _print_Category(self, category):
        return 'Category("%s")' % category.name

    def _print_BaseScalarField(self, field):
        return field._coord_sys._names[field._index]

    def _print_BaseVectorField(self, field):
        return 'e_%s' % field._coord_sys._names[field._index]

    def _print_Differential(self, diff):
        field = diff._form_field
        if hasattr(field, '_coord_sys'):
            return 'd%s' % field._coord_sys._names[field._index]
        else:
            return 'd(%s)' % self._print(field)

    def _print_Tr(self, expr):
        # TODO : Handle indices
        return "%s(%s)" % ("Tr", self._print(expr.args[0]))


def sstr(expr, **settings):
    """Returns the expression as a string.

    For large expressions where speed is a concern, use the setting
    order='none'. If abbrev=True setting is used then units are printed in
    abbreviated form.

    Examples
    ========

    >>> from sympy import symbols, Eq, sstr
    >>> a, b = symbols('a b')
    >>> sstr(Eq(a + b, 0))
    'Eq(a + b, 0)'
    """

    p = StrPrinter(settings)
    s = p.doprint(expr)

    return s


class StrReprPrinter(StrPrinter):
    """(internal) -- see sstrrepr"""

    def _print_str(self, s):
        return repr(s)


def sstrrepr(expr, **settings):
    """return expr in mixed str/repr form

       i.e. strings are returned in repr form with quotes, and everything else
       is returned in str form.

       This function could be useful for hooking into sys.displayhook
    """

    p = StrReprPrinter(settings)
    s = p.doprint(expr)

    return s
