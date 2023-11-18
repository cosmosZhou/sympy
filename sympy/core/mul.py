from collections import defaultdict
from functools import cmp_to_key
import operator

from .sympify import sympify
from .basic import Basic
from .singleton import S
from .operations import AssocOp, AssocOpDispatcher
from .cache import cacheit
from .logic import fuzzy_not, _fuzzy_group
from .compatibility import reduce
from .expr import Expr
from .parameters import global_parameters


# internal marker to indicate:
#   "there are still non-commutative objects -- don't forget to process them"
class NC_Marker:
    is_Order = False
    is_Mul = False
    is_Number = False
    is_Poly = False

    is_commutative = False


# Key for sorting commutative args in canonical order
_args_sortkey = cmp_to_key(Basic.compare)


def _mulsort(args):
    # in-place sorting of args
    args.sort(key=_args_sortkey)


def _unevaluated_Mul(*args):
    """Return a well-formed unevaluated Mul: Numbers are collected and
    put in slot 0, any arguments that are Muls will be flattened, and args
    are sorted. Use this when args have changed but you still want to return
    an unevaluated Mul.

    Examples
    ========

    >>> from sympy.core.mul import _unevaluated_Mul as uMul
    >>> from sympy import S, sqrt, Mul
    >>> from sympy.abc import x
    >>> a = uMul(*[S(3.0), x, S(2)])
    >>> a.args[0]
    6.00000000000000
    >>> a.args[1]
    x

    Two unevaluated Muls with the same arguments will
    always compare as equal during testing:

    >>> m = uMul(sqrt(2), sqrt(3))
    >>> m == uMul(sqrt(3), sqrt(2))
    True
    >>> u = Mul(sqrt(3), sqrt(2), evaluate=False)
    >>> m == uMul(u)
    True
    >>> m == Mul(*m.args)
    False

    """
    args = list(args)
    newargs = []
    ncargs = []
    co = S.One
    while args:
        a = args.pop()
        if a.is_Mul:
            c, nc = a.args_cnc()
            args.extend(c)
            if nc:
                ncargs.append(Mul._from_args(nc))
        elif a.is_Number:
            co *= a
        else:
            newargs.append(a)
    _mulsort(newargs)
    if co is not S.One:
        newargs.insert(0, co)
    if ncargs:
        newargs.append(Mul._from_args(ncargs))
    return Mul._from_args(newargs)


class Mul(Expr, AssocOp):

    __slots__ = ()

    is_commutative = True

    def __neg__(self):
        c, args = self.as_coeff_mul()
        c = -c
        if c is not S.One:
            if args[0].is_Number:
                args = list(args)
                if c is S.NegativeOne:
                    args[0] = -args[0]
                else:
                    args[0] *= c
            elif args[0]._coeff_isneg():
                args = (-args[0], *args[1:])
            else:
                args = (c,) + args
        return self._from_args(args, self.is_commutative)
    
    def _coeff_isneg(self):
        """Return True if the leading Number is negative.
    
        Examples
        ========
    
        >>> from sympy.core.function import _coeff_isneg
        >>> from sympy import S, Symbol, oo, pi
        >>> _coeff_isneg(-3*pi)
        True
        >>> _coeff_isneg(S(3))
        False
        >>> _coeff_isneg(-oo)
        True
        >>> _coeff_isneg(Symbol('n', negative=True)) # coeff is 1
        False
    
        For matrix expressions:
    
        >>> from sympy import MatrixSymbol, sqrt
        >>> A = MatrixSymbol("A", 3, 3)
        >>> _coeff_isneg(-sqrt(2)*A)
        True
        >>> _coeff_isneg(sqrt(2)*A)
        False
        """ 
        return self.args[0]._coeff_isneg()

    @classmethod
    def flatten(cls, seq):
        """Return commutative, noncommutative and order arguments by
        combining related terms.

        Notes
        =====
            * In an expression like ``a*b*c``, python process this through sympy
              as ``Mul(Mul(a, b), c)``. This can have undesirable consequences.

              -  Sometimes terms are not combined as one would like:
                 {c.f. https://github.com/sympy/sympy/issues/4596}

                >>> from sympy import Mul, sqrt
                >>> from sympy.abc import x, y, z
                >>> 2*(x + 1) # this is the 2-arg Mul behavior
                2*x + 2
                >>> y*(x + 1)*2
                2*y*(x + 1)
                >>> 2*(x + 1)*y # 2-arg result will be obtained first
                y*(2*x + 2)
                >>> Mul(2, x + 1, y) # all 3 args simultaneously processed
                2*y*(x + 1)
                >>> 2*((x + 1)*y) # parentheses can control this behavior
                2*y*(x + 1)

                Powers with compound bases may not find a single base to
                combine with unless all arguments are processed at once.
                Post-processing may be necessary in such cases.
                {c.f. https://github.com/sympy/sympy/issues/5728}

                >>> a = sqrt(x*sqrt(y))
                >>> a**3
                (x*sqrt(y))**(3/2)
                >>> Mul(a,a,a)
                (x*sqrt(y))**(3/2)
                >>> a*a*a
                x*sqrt(y)*sqrt(x*sqrt(y))
                >>> _.subs(a.base, z).subs(z, a.base)
                (x*sqrt(y))**(3/2)

              -  If more than two terms are being multiplied then all the
                 previous terms will be re-processed for each new argument.
                 So if each of ``a``, ``b`` and ``c`` were :class:`Mul`
                 expression, then ``a*b*c`` (or building up the product
                 with ``*=``) will process all the arguments of ``a`` and
                 ``b`` twice: once when ``a*b`` is computed and again when
                 ``c`` is multiplied.

                 Using ``Mul(a, b, c)`` will process all arguments once.

            * The results of Mul are cached according to arguments, so flatten
              will only be called once for ``Mul(a, b, c)``. If you can
              structure a calculation so the arguments are most likely to be
              repeats then this can save time in computing the answer. For
              example, say you had a Mul, M, that you wished to divide by ``d[i]``
              and multiply by ``n[i]`` and you suspect there are many repeats
              in ``n``. It would be better to compute ``M*n[i]/d[i]`` rather
              than ``M/d[i]*n[i]`` since every time n[i] is a repeat, the
              product, ``M*n[i]`` will be returned without flattening -- the
              cached value will be returned. If you divide by the ``d[i]``
              first (and those are more unique than the ``n[i]``) then that will
              create a new Mul, ``M/d[i]`` the args of which will be traversed
              again when it is multiplied by ``n[i]``.

              {c.f. https://github.com/sympy/sympy/issues/5706}

              This consideration is moot if the cache is turned off.

            NB
            --
              The validity of the above notes depends on the implementation
              details of Mul and flatten which may change at any time. Therefore,
              you should only consider them when your code is highly performance
              sensitive.

              Removal of 1 from the sequence is already handled by AssocOp.__new__.
        """

        from sympy.calculus.util import AccumBounds
        from sympy.matrices.expressions import MatrixExpr
        from sympy.matrices.expressions.matexpr import ZeroMatrix
        rv = None
        
        infinitesimals = [x for x in seq if x.infinitesimality is not None]
        infinitesimal = None
        if infinitesimals:
            noninfinitesimals = [x for x in seq if x.infinitesimality is None]
            if len(infinitesimals) == 1:
                infinitesimal, *_ = infinitesimals
                noninfinitesimal, infinitesimal = infinitesimal.clear_infinitesimal()
                sign = 1
                for coeff in noninfinitesimals:
                    if coeff.is_extended_positive:
                        continue
                    if coeff.is_extended_negative:
                        sign *= -1
                        continue
                    raise Exception('could not determine the final infinitesimal value in the expression: ', seq)
                infinitesimal *= sign
                if noninfinitesimal.is_zero: 
                    return [noninfinitesimal], [], infinitesimal
                seq = noninfinitesimals + [noninfinitesimal]
            else:
                raise Exception('could not determine the final infinitesimal value in the expression: ', seq)
                
        if len(seq) == 2:
            a, b = seq
            if b.is_Rational:
                a, b = b, a
                seq = [a, b]
                
            if not a.is_zero and a.is_Rational:
                r, b = b.as_coeff_Mul()
                if b.is_Add:
                    if r is not S.One:  # 2-arg hack
                        # leave the Mul as a Mul?
                        ar = a * r
                        if ar is S.One:
                            arb = b
                        else:
                            arb = cls(a * r, b, evaluate=False)
                        rv = [arb], [], None
                    elif global_parameters.distribute:  # and b.is_commutative:
                        r, b = b.as_coeff_Add()
                        bargs = [_keep_coeff(a, bi) for bi in Add.make_args(b)]
                        _addsort(bargs)
                        ar = a * r
                        if ar:
                            bargs.insert(0, ar)
                        bargs = [Add._from_args(bargs)]
                        rv = bargs, [], None
            if rv:
                return rv

        # apply associativity, separate commutative part of seq
        c_part = []  # out: commutative factors
        nc_part = []  # out: non-commutative factors

        coeff = S.One  # standalone term
                            # e.g. 3 * ...
                            
        c_powers = []  # (base,exp)      n
                            # e.g. (x,n) for x

        num_exp = []  # (num-base, exp)           y
                            # e.g.  (3, y)  for  ... * 3  * ...

        neg1e = S.Zero  # exponent on -1 extracted from Number-based Pow and I

        pnum_rat = {}  # (num-base, Rat-exp)          1/2
                            # e.g.  (3, 1/2)  for  ... * 3     * ...

        order_symbols = None

        # --- PART 1 ---
        #
        # "collect powers and coeff":
        #
        # o coeff
        # o c_powers
        # o num_exp
        # o neg1e
        # o pnum_rat
        #
        # NOTE: this is optimized for all-objects-are-commutative case
        for o in seq:
            # O(x)
            if o.is_Order:
                o, order_symbols = o.as_expr_variables(order_symbols)

            if o.is_Mul:
                seq.extend(o.args)  # XXX zerocopy?
                continue

            # 3
            elif o.is_Number:
                if o is S.NaN or coeff is S.ComplexInfinity and o.is_zero:
                    # we know for sure the result will be nan
                    return [S.NaN], [], None
                elif coeff.is_Number or isinstance(coeff, AccumBounds):  # it could be zoo
                    coeff *= o
                    if coeff is S.NaN:
                        # we know for sure the result will be nan
                        return [S.NaN], [], None
                elif o.is_infinite:
                    c_powers.append((o, S.One))
                elif o.is_NegativeOne:
                    coeff = -coeff
                continue

            elif isinstance(o, AccumBounds):
                coeff = o.__mul__(coeff)
                continue

            elif o is S.ComplexInfinity:
                if not coeff:
                    # 0 * zoo = NaN
                    return [S.NaN], [], None
                coeff = S.ComplexInfinity
                continue

            elif o is S.ImaginaryUnit:
                neg1e += S.Half
                continue

            elif o.is_ZeroMatrix:
                coeff = o * coeff
                continue
            elif o.is_OneMatrix:
                if len(coeff.shape) < len(o.shape):
                    if coeff.is_infinite and c_powers:
                        indices_to_be_deleted = []
                        for i, (b, e) in enumerate(c_powers):
                            if not b.shape and not e.shape:
                                if e.is_real and b.is_positive:
                                    indices_to_be_deleted.append(i)
                                elif e.is_integer and e.is_odd and b.is_negative:
                                    coeff = -coeff
                                    indices_to_be_deleted.append(i)
                        if indices_to_be_deleted:
                            indices_to_be_deleted.reverse()
                            for index in indices_to_be_deleted:
                                del c_powers[index]
                    elif coeff.is_Zero or coeff.is_ZeroMatrix:
                        coeff = ZeroMatrix(*o.shape)
                        o = coeff
                                     
                    coeff = Mul(coeff, o, evaluate=False)
                continue
            else:
                #      e
                # o = b
                if not o.shape and coeff.is_infinite:
                    if o.is_positive:
                        continue
                    elif o.is_negative:
                        coeff = -coeff
                        continue
                        
                b, e = o.as_base_exp()

                #  y
                # 3
                if o.is_Pow:
                    if b.is_Number:

                        # get all the factors with numeric base so they can be
                        # combined below, but don't combine negatives unless
                        # the exponent is an integer
                        if e.is_Rational:
                            if e.is_Integer:
                                coeff *= Pow(b, e)  # it is an unevaluated power
                                continue
                            elif e.is_negative:  # also a sign of an unevaluated power
                                seq.append(Pow(b, e))
                                continue
                            elif b.is_negative:
                                neg1e += e
                                b = -b
                            if b is not S.One:
                                pnum_rat.setdefault(b, []).append(e)
                            continue
                        elif b.is_positive or e.is_integer:
                            num_exp.append((b, e))
                            continue

                c_powers.append((b, e))

        # We do want a combined exponent if it would not be an Add, such as
        #  y    2y     3y
        # x  * x   -> x
        # We determine if two exponents have the same term by using
        # as_coeff_Mul.
        #
        # Unfortunately, this isn't smart enough to consider combining into
        # exponents that might already be adds, so things like:
        #  z - y    y
        # x      * x  will be left alone.  This is because checking every possible
        # combination can slow things down.

        # gather exponents of common bases...
        def _gather(c_powers):
            common_b = {}  # b:e
            for b, e in c_powers:
                co = e.as_coeff_Mul()
                common_b.setdefault(b, {}).setdefault(co[1], []).append(co[0])
            for b, d in common_b.items():
                for di, li in d.items():
                    d[di] = Add(*li)
            new_c_powers = []
            for b, e in common_b.items():
                new_c_powers.extend([(b, c * t) for t, c in e.items()])
            return new_c_powers

        # in c_powers
        c_powers = _gather(c_powers)

        # and in num_exp
        num_exp = _gather(num_exp)

        # --- PART 2 ---
        #
        # o process collected powers  (x**0 -> 1; x**1 -> x; otherwise Pow)
        # o combine collected powers  (2**x * 3**x -> 6**x)
        #   with numeric base

        # ................................
        # now we have:
        # - coeff:
        # - c_powers:    (b, e)
        # - num_exp:     (2, e)
        # - pnum_rat:    {(1/3, [1/3, 2/3, 1/4])}

        #  0             1
        # x  -> 1       x  -> x

        # this should only need to run twice; if it fails because
        # it needs to be run more times, perhaps this should be
        # changed to a "while True" loop -- the only reason it
        # isn't such now is to allow a less-than-perfect result to
        # be obtained rather than raising an error or entering an
        # infinite loop
        for _ in range(2):
            new_c_powers = []
            changed = False
            for b, e in c_powers:
                if e.is_zero:
                    # canceling out infinities yields NaN
                    if (b.is_Add or b.is_Mul) and any(infty in b.args
                        for infty in (S.ComplexInfinity, S.Infinity,
                                      S.NegativeInfinity)):
                        return [S.NaN], [], None
                    continue
                if e is S.One:
                    if b.is_Number:
                        if not b.is_infinite:
                            coeff *= b
                            continue
                    p = b
                if e is not S.One:
                    p = Pow(b, e)
                    # check to make sure that the base doesn't change
                    # after exponentiation; to allow for unevaluated
                    # Pow, we only do so if b is not already a Pow
                    if p.is_Pow and not b.is_Pow:
                        bi = b
                        b, e = p.as_base_exp()
                        if b != bi:
                            changed = True
                c_part.append(p)
                new_c_powers.append((b, e))
            # there might have been a change, but unless the base
            # matches some other base, there is nothing to do
            if changed and len({
                    b for b, e in new_c_powers}) != len(new_c_powers):
                # start over again
                c_part = []
                c_powers = _gather(new_c_powers)
            else:
                break

        #  x    x     x
        # 2  * 3  -> 6
        inv_exp_dict = {}  # exp:Mul(num-bases)     x    x
                            # e.g.  x:6  for  ... * 2  * 3  * ...
        for b, e in num_exp:
            inv_exp_dict.setdefault(e, []).append(b)
        for e, b in inv_exp_dict.items():
            inv_exp_dict[e] = cls(*b)
        c_part.extend([Pow(b, e) for e, b in inv_exp_dict.items() if e])

        # b, e -> e' = sum(e), b
        # {(1/5, [1/3]), (1/2, [1/12, 1/4]} -> {(1/3, [1/5, 1/2])}
        comb_e = {}
        for b, e in pnum_rat.items():
            comb_e.setdefault(Add(*e), []).append(b)
        del pnum_rat
        # process them, reducing exponents to values less than 1
        # and updating coeff if necessary else adding them to
        # num_rat for further processing
        num_rat = []
        for e, b in comb_e.items():
            b = cls(*b)
            if e.q == 1:
                coeff *= Pow(b, e)
                continue
            if e.p > e.q:
                e_i, ep = divmod(e.p, e.q)
                coeff *= Pow(b, e_i)
                e = Rational(ep, e.q)
            num_rat.append((b, e))
        del comb_e

        # extract gcd of bases in num_rat
        # 2**(1/3)*6**(1/4) -> 2**(1/3+1/4)*3**(1/4)
        pnew = defaultdict(list)
        i = 0  # steps through num_rat which may grow
        while i < len(num_rat):
            bi, ei = num_rat[i]
            grow = []
            for j in range(i + 1, len(num_rat)):
                bj, ej = num_rat[j]
                g = bi.gcd(bj)
                if g is not S.One:
                    # 4**r1*6**r2 -> 2**(r1+r2)  *  2**r1 *  3**r2
                    # this might have a gcd with something else
                    e = ei + ej
                    if e.q == 1:
                        coeff *= Pow(g, e)
                    else:
                        if e.p > e.q:
                            e_i, ep = divmod(e.p, e.q)  # change e in place
                            coeff *= Pow(g, e_i)
                            e = Rational(ep, e.q)
                        grow.append((g, e))
                    # update the jth item
                    num_rat[j] = (bj / g, ej)
                    # update bi that we are checking with
                    bi = bi / g
                    if bi is S.One:
                        break
            if bi is not S.One:
                obj = Pow(bi, ei)
                if obj.is_Number:
                    coeff *= obj
                else:
                    # changes like sqrt(12) -> 2*sqrt(3)
                    for obj in Mul.make_args(obj):
                        if obj.is_Number:
                            coeff *= obj
                        else:
                            assert obj.is_Pow
                            bi, ei = obj.args
                            pnew[ei].append(bi)

            num_rat.extend(grow)
            i += 1

        # combine bases of the new powers
        for e, b in pnew.items():
            pnew[e] = cls(*b)

        # handle -1 and I
        if neg1e:
            # treat I as (-1)**(1/2) and compute -1's total exponent
            p, q = neg1e.as_numer_denom()
            # if the integer part is odd, extract -1
            n, p = divmod(p, q)
            if n % 2:
                coeff = -coeff
            # if it's a multiple of 1/2 extract I
            if q == 2:
                c_part.append(S.ImaginaryUnit)
            elif p:
                # see if there is any positive base this power of
                # -1 can join
                neg1e = Rational(p, q)
                for e, b in pnew.items():
                    if e == neg1e and b.is_positive:
                        pnew[e] = -b
                        break
                else:
                    # keep it separate; we've already evaluated it as
                    # much as possible so evaluate=False
                    c_part.append(Pow(S.NegativeOne, neg1e, evaluate=False))

        # add all the pnew powers
        c_part.extend([Pow(b, e) for e, b in pnew.items()])

        # oo, -oo
        if (coeff is S.Infinity) or (coeff is S.NegativeInfinity):

            def _handle_for_oo(c_part, coeff_sign):
                new_c_part = []
                for t in c_part:
                    if t.is_extended_positive:
                        continue
                    if t.is_extended_negative:
                        coeff_sign *= -1
                        continue
                    new_c_part.append(t)
                return new_c_part, coeff_sign

            c_part, coeff_sign = _handle_for_oo(c_part, 1)
            nc_part, coeff_sign = _handle_for_oo(nc_part, coeff_sign)
            coeff *= coeff_sign

        if (coeff is S.Infinitesimal) or (coeff is S.NegativeInfinitesimal):

            def _handle_for_infinitesimal(c_part, coeff_sign):
                new_c_part = []
                for t in c_part:
                    if t.is_extended_positive:
                        continue
                    if t.is_extended_negative:
                        coeff_sign *= -1
                        continue
                    new_c_part.append(t)
                return new_c_part, coeff_sign

            c_part, coeff_sign = _handle_for_infinitesimal(c_part, 1)
            nc_part, coeff_sign = _handle_for_infinitesimal(nc_part, coeff_sign)
            coeff *= coeff_sign

        # zoo
        if coeff is S.ComplexInfinity:
            # zoo might be
            #   infinite_real + bounded_im
            #   bounded_real + infinite_im
            #   infinite_real + infinite_im
            # and non-zero real or imaginary will not change that status.
            c_part = [c for c in c_part if not (fuzzy_not(c.is_zero) and
                                                c.is_extended_real is not None)]
            nc_part = [c for c in nc_part if not (fuzzy_not(c.is_zero) and
                                                  c.is_extended_real is not None)]

        # 0
        elif coeff.is_zero:
            # we know for sure the result will be 0 / ZeroMatrix except the multiplicand
            # is infinity or a matrix
            if any(isinstance(c, MatrixExpr) for c in nc_part):
                return [coeff], nc_part, order_symbols
            if any(c.is_finite == False for c in c_part):
                return [S.NaN], [], order_symbols
            
            shape = Add.broadcast_from_sequence(seq)
            coeff = ZeroMatrix(*shape)
            return [coeff], [], order_symbols

        # check for straggling Numbers that were produced
        _new = []
        for i in c_part:
            if i.is_Number and not i.is_infinite:
                coeff *= i
            else:
                _new.append(i)
        c_part = _new

        # order commutative part canonically
        _mulsort(c_part)

        # current code expects coeff to be always in slot-0
        if coeff.is_One:
            ...
        elif coeff.is_OneMatrix:
            if not c_part or len(coeff.shape) > max((len(arg.shape) for arg in c_part)):
                c_part.insert(0, coeff)
        elif coeff.is_Mul:
            c_part = [*coeff.args] + c_part
        else:
            c_part.insert(0, coeff)

        # we are done
        if (global_parameters.distribute and not nc_part and len(c_part) == 2 and
                c_part[0].is_Number and c_part[0].is_finite and c_part[1].is_Add):
            # 2*(1+a) -> 2 + 2 * a
            coeff = c_part[0]
            c_part = [Add(*[coeff * f for f in c_part[1].args])]

        if infinitesimal:
            return c_part, nc_part, infinitesimal
        return c_part, nc_part, order_symbols

    def _eval_power(self, e):

        # don't break up NC terms: (A*B)**3 != A**3*B**3, it is A*B*A*B*A*B
        cargs, nc = self.args_cnc(split_1=False)

        if e.is_Integer:
            return Mul(*[Pow(b, e, evaluate=False) for b in cargs]) * \
                Pow(Mul._from_args(nc), e, evaluate=False)
        if e.is_Rational and e.q == 2:
            from sympy.core.power import integer_nthroot
            from sympy.functions.elementary.complexes import sign
            if self.is_imaginary:
                a = self.as_real_imag()[1]
                if a.is_Rational:
                    n, d = abs(a / 2).as_numer_denom()
                    n, t = integer_nthroot(n, 2)
                    if t:
                        d, t = integer_nthroot(d, 2)
                        if t:
                            r = sympify(n) / d
                            return _unevaluated_Mul(r ** e.p, (1 + sign(a) * S.ImaginaryUnit) ** e.p)

        p = Pow(self, e, evaluate=False)

        if e.is_Rational or e.is_Float:
            return p._eval_expand_power_base()

        return p

    @classmethod
    def class_key(cls):
        return 3, 0, cls.__name__

    def _eval_evalf(self, prec):
        c, m = self.as_coeff_Mul()
        if c is S.NegativeOne:
            if m.is_Mul:
                rv = -AssocOp._eval_evalf(m, prec)
            else:
                mnew = m._eval_evalf(prec)
                if mnew is not None:
                    m = mnew
                rv = -m
        else:
            rv = AssocOp._eval_evalf(self, prec)
        if rv.is_number:
            return rv.expand()
        return rv

    @property
    def _mpc_(self):
        """
        Convert self to an mpmath mpc if possible
        """
        from sympy.core.numbers import I, Float
        im_part, imag_unit = self.as_coeff_Mul()
        if not imag_unit == I:
            # ValueError may seem more reasonable but since it's a @property,
            # we need to use AttributeError to keep from confusing things like
            # hasattr.
            raise AttributeError("Cannot convert Mul to mpc. Must be of the form Number*I")

        return (Float(0)._mpf_, Float(im_part)._mpf_)

    @cacheit
    def as_two_terms(self):
        """Return head and tail of self.

        This is the most efficient way to get the head and tail of an
        expression.

        - if you want only the head, use self.args[0];
        - if you want to process the arguments of the tail then use
          self.as_coef_mul() which gives the head and a tuple containing
          the arguments of the tail when treated as a Mul.
        - if you want the coefficient when self is treated as an Add
          then use self.as_coeff_add()[0]

        Examples
        ========

        >>> from sympy.abc import x, y
        >>> (3*x*y).as_two_terms()
        (3, x*y)
        """
        args = self.args

        if len(args) == 1:
            return S.One, self
        elif len(args) == 2:
            return args

        else:
            return args[0], self._new_rawargs(*args[1:])

    @cacheit
    def as_coefficients_dict(self):
        """Return a dictionary mapping terms to their coefficient.
        Since the dictionary is a defaultdict, inquiries about terms which
        were not present will return a coefficient of 0. The dictionary
        is considered to have a single term.

        Examples
        ========

        >>> from sympy.abc import a, x
        >>> (3*a*x).as_coefficients_dict()
        {a*x: 3}
        >>> _[a]
        0
        """

        d = defaultdict(int)
        args = self.args

        if len(args) == 1 or not args[0].is_Number:
            d[self] = S.One
        else:
            d[self._new_rawargs(*args[1:])] = args[0]

        return d

    @cacheit
    def as_coeff_mul(self, *deps, rational=True, **kwargs):
        if deps:
            from sympy.utilities.iterables import sift
            l1, l2 = sift(self.args, lambda x: x.has(*deps), binary=True)
            return self._new_rawargs(*l2), tuple(l1)
        args = self.args
        if args[0].is_Number:
            if not rational or args[0].is_Rational:
                return args[0], args[1:]
            elif args[0].is_extended_negative:
                return S.NegativeOne, (-args[0],) + args[1:]
        return S.One, args

    def as_coeff_Mul(self, rational=False):
        """
        Efficiently extract the coefficient of a product.
        """
        coeff, args = self.args[0], self.args[1:]

        if coeff.is_Number:
            if not rational or coeff.is_Rational:
                if len(args) == 1:
                    return coeff, args[0]
                else:
                    return coeff, self._new_rawargs(*args)
            elif coeff.is_extended_negative:
                return S.NegativeOne, self._new_rawargs(*((-coeff,) + args))
        return S.One, self

    def as_real_imag(self, deep=True, **hints):
        from sympy import Abs, expand_mul, Im, Re
        other = []
        coeffr = []
        coeffi = []
        addterms = S.One
        for a in self.args:
            r, i = a.as_real_imag()
            if i.is_zero:
                coeffr.append(r)
            elif r.is_zero:
                coeffi.append(i * S.ImaginaryUnit)
#             elif a.is_commutative:
            else:
                # search for complex conjugate pairs:
                for i, x in enumerate(other):
                    if x == a.conjugate():
                        coeffr.append(Abs(x) ** 2)
                        del other[i]
                        break
                else:
                    if a.is_Add:
                        addterms *= a
                    else:
                        other.append(a)
#             else:
#                 other.append(a)
        m = self.func(*other)
        if hints.get('ignore') == m:
            return
        if len(coeffi) % 2:
            imco = Im(coeffi.pop(0))
            # all other pairs make a real factor; they will be
            # put into reco below
        else:
            imco = S.Zero
        reco = self.func(*(coeffr + coeffi))
        r, i = (reco * Re(m), reco * Im(m))
        if addterms == 1:
            if m == 1:
                if imco.is_zero:
                    return (reco, S.Zero)
                else:
                    return (S.Zero, reco * imco)
            if imco is S.Zero:
                return (r, i)
            return (-imco * i, imco * r)
        addre, addim = expand_mul(addterms, deep=False).as_real_imag()
        if imco is S.Zero:
            return (r * addre - i * addim, i * addre + r * addim)
        else:
            r, i = -imco * i, imco * r
            return (r * addre - i * addim, r * addim + i * addre)

    @staticmethod
    def _expandsums(sums):
        """
        Helper function for _eval_expand_mul.

        sums must be a list of instances of Basic.
        """

        L = len(sums)
        if L == 1:
            return sums[0].args
        terms = []
        left = Mul._expandsums(sums[:L // 2])
        right = Mul._expandsums(sums[L // 2:])

        terms = [Mul(a, b) for a in left for b in right]
        added = Add(*terms)
        return Add.make_args(added)  # it may have collapsed down to one term

    def _eval_expand_mul(self, **hints):
        from sympy import fraction

        # Handle things like 1/(x*(x + 1)), which are automatically converted
        # to 1/x*1/(x + 1)
        expr = self
        n, d = fraction(expr)
        if d.is_Mul:
            n, d = [i._eval_expand_mul(**hints) if i.is_Mul else i
                for i in (n, d)]
            expr = n / d
            if not expr.is_Mul:
                return expr

        plain, sums, rewrite = [], [], False
        for factor in expr.args:
            if factor.is_Add:
                sums.append(factor)
                rewrite = True
            else:
#                 if factor.is_commutative:
                plain.append(factor)
#                 else:
#                     sums.append(Basic(factor))  # Wrapper

        if not rewrite:
            return expr
        else:
            plain = self.func(*plain)
            if sums:
                deep = hints.get("deep", False)
                terms = self.func._expandsums(sums)
                args = []
                for term in terms:
                    t = self.func(plain, term)
                    if t.is_Mul and any(a.is_Add for a in t.args) and deep:
                        t = t._eval_expand_mul()
                    args.append(t)
                return Add(*args)
            else:
                return plain

    @cacheit
    def _eval_derivative(self, s):
        args = list(self.args)
        terms = []
        for i in range(len(args)):
            d = args[i].diff(s)
            if d:
                # Note: reduce is used in step of Mul as Mul is unable to
                # handle subtypes and operation priority:
                terms.append(reduce(lambda x, y: x * y, (args[:i] + [d] + args[i + 1:]), S.One))
        return Add.fromiter(terms)

    @cacheit
    def _eval_derivative_n_times(self, s, n):
        from sympy import Integer, factorial, prod, Sum, Max
        from sympy.ntheory.multinomial import multinomial_coefficients_iterator
        from .function import AppliedUndef
        from .symbol import Symbol, symbols, Dummy
        if not isinstance(s, AppliedUndef) and not isinstance(s, Symbol):
            # other types of s may not be well behaved, e.g.
            # (cos(x)*sin(y)).diff([[x, y, z]])
            return super()._eval_derivative_n_times(s, n)
        args = self.args
        m = len(args)
        if isinstance(n, (int, Integer)):
            # https://en.wikipedia.org/wiki/General_Leibniz_rule#More_than_two_factors
            terms = []
            for kvals, c in multinomial_coefficients_iterator(m, n):
                p = prod([arg.diff((s, k)) for k, arg in zip(kvals, args)])
                terms.append(c * p)
            return Add(*terms)
        kvals = symbols("k1:%i" % m, cls=Dummy)
        klast = n - sum(kvals)
        nfact = factorial(n)
        e, l = (# better to use the multinomial?
            nfact / prod(map(factorial, kvals)) / factorial(klast) * \
            prod([args[t].diff((s, kvals[t])) for t in range(m - 1)]) * \
            args[-1].diff((s, Max(0, klast))),
            [(k, 0, n) for k in kvals])
        return Sum(e, *l)

    def _eval_determinant(self, **kwargs):
        if len(self.args) == 2:
            x, A = self.args
            if len(x.shape) == 2 and len(A.shape) == 1:
                tmp = A
                A = x
                x = tmp
            if len(x.shape) == 1 and len(A.shape) == 2:
                from sympy import Product, det
                n = x.shape[0]
                i = x.generate_var(integer=True)
                return det(A) * Product[i:n](x[i])

    def _eval_difference_delta(self, n, step):
        from sympy.series.limitseq import difference_delta as dd
        arg0 = self.args[0]
        rest = Mul(*self.args[1:])
        return (arg0.subs(n, n + step) * dd(rest, n, step) + dd(arg0, n, step) * 
                rest)

    def _matches_simple(self, expr, repl_dict):
        # handle (w*3).matches('x*5') -> {w: x*5/3}
        coeff, terms = self.as_coeff_Mul()
        terms = Mul.make_args(terms)
        if len(terms) == 1:
            newexpr = self.__class__._combine_inverse(expr, coeff)
            return terms[0].matches(newexpr, repl_dict)
        return

    def matches(self, expr, repl_dict={}, old=False):
        expr = sympify(expr)
        repl_dict = repl_dict.copy()
#         if self.is_commutative and expr.is_commutative:
        return AssocOp._matches_commutative(self, expr, repl_dict, old)
#         elif self.is_commutative is not expr.is_commutative:
#             return None
        c1, nc1 = self.args_cnc()
        c2, nc2 = expr.args_cnc()
        c1, c2 = [c or [1] for c in [c1, c2]]

        # TODO: Should these be self.func?
        comm_mul_self = Mul(*c1)
        comm_mul_expr = Mul(*c2)

        repl_dict = comm_mul_self.matches(comm_mul_expr, repl_dict, old)

        # If the commutative arguments didn't match and aren't equal, then
        # then the expression as a whole doesn't match
        if repl_dict is None and c1 != c2:
            return None

        # Now match the non-commutative arguments, expanding powers to
        # multiplications
        nc1 = Mul._matches_expand_pows(nc1)
        nc2 = Mul._matches_expand_pows(nc2)

        repl_dict = Mul._matches_noncomm(nc1, nc2, repl_dict)

        return repl_dict or None

    def _matches(self, expr, repl_dict={}):
        # weed out negative one prefixes#
        from sympy import Wild
        sign = 1
        a, b = self.as_two_terms()
        if a is S.NegativeOne:
            if b.is_Mul:
                sign = -sign
            else:
                # the remainder, b, is not a Mul anymore
                return b.matches(-expr, repl_dict)
        expr = sympify(expr)
        if expr.is_Mul and expr.args[0] is S.NegativeOne:
            expr = -expr
            sign = -sign

        if not expr.is_Mul:
            # expr can only match if it matches b and a matches +/- 1
            if len(self.args) == 2:
                # quickly test for equality
                if b == expr:
                    return a.matches(Rational(sign), repl_dict)
                # do more expensive match
                dd = b.matches(expr, repl_dict)
                if dd is None:
                    return None
                dd = a.matches(Rational(sign), dd)
                return dd
            return None

        d = repl_dict.copy()

        # weed out identical terms
        pp = list(self.args)
        ee = list(expr.args)
        for p in self.args:
            if p in expr.args:
                ee.remove(p)
                pp.remove(p)

        # only one symbol left in pattern -> match the remaining expression
        if len(pp) == 1 and isinstance(pp[0], Wild):
            if len(ee) == 1:
                d[pp[0]] = sign * ee[0]
            else:
                d[pp[0]] = sign * expr.func(*ee)
            return d

        if len(ee) != len(pp):
            return None

        for p, e in zip(pp, ee):
            d = p.xreplace(d).matches(e, d)
            if d is None:
                return None
        return d

    @staticmethod
    def _matches_expand_pows(arg_list):
        new_args = []
        for arg in arg_list:
            if arg.is_Pow and arg.exp > 0:
                new_args.extend([arg.base] * arg.exp)
            else:
                new_args.append(arg)
        return new_args

    @staticmethod
    def _matches_noncomm(nodes, targets, repl_dict={}):
        """Non-commutative multiplication matcher.

        `nodes` is a list of symbols within the matcher multiplication
        expression, while `targets` is a list of arguments in the
        multiplication expression being matched against.
        """
        repl_dict = repl_dict.copy()
        # List of possible future states to be considered
        agenda = []
        # The current matching state, storing index in nodes and targets
        state = (0, 0)
        node_ind, target_ind = state
        # Mapping between wildcard indices and the index ranges they match
        wildcard_dict = {}
        repl_dict = repl_dict.copy()

        while target_ind < len(targets) and node_ind < len(nodes):
            node = nodes[node_ind]

            if node.is_Wild:
                Mul._matches_add_wildcard(wildcard_dict, state)

            states_matches = Mul._matches_new_states(wildcard_dict, state,
                                                     nodes, targets)
            if states_matches:
                new_states, new_matches = states_matches
                agenda.extend(new_states)
                if new_matches:
                    for match in new_matches:
                        repl_dict[match] = new_matches[match]
            if not agenda:
                return None
            else:
                state = agenda.pop()
                node_ind, target_ind = state

        return repl_dict

    @staticmethod
    def _matches_add_wildcard(dictionary, state):
        node_ind, target_ind = state
        if node_ind in dictionary:
            begin, end = dictionary[node_ind]
            dictionary[node_ind] = (begin, target_ind)
        else:
            dictionary[node_ind] = (target_ind, target_ind)

    @staticmethod
    def _matches_new_states(dictionary, state, nodes, targets):
        node_ind, target_ind = state
        node = nodes[node_ind]
        target = targets[target_ind]

        # Don't advance at all if we've exhausted the targets but not the nodes
        if target_ind >= len(targets) - 1 and node_ind < len(nodes) - 1:
            return None

        if node.is_Wild:
            match_attempt = Mul._matches_match_wilds(dictionary, node_ind,
                                                     nodes, targets)
            if match_attempt:
                # If the same node has been matched before, don't return
                # anything if the current match is diverging from the previous
                # match
                other_node_inds = Mul._matches_get_other_nodes(dictionary,
                                                               nodes, node_ind)
                for ind in other_node_inds:
                    other_begin, other_end = dictionary[ind]
                    curr_begin, curr_end = dictionary[node_ind]

                    other_targets = targets[other_begin:other_end + 1]
                    current_targets = targets[curr_begin:curr_end + 1]

                    for curr, other in zip(current_targets, other_targets):
                        if curr != other:
                            return None

                # A wildcard node can match more than one target, so only the
                # target index is advanced
                new_state = [(node_ind, target_ind + 1)]
                # Only move on to the next node if there is one
                if node_ind < len(nodes) - 1:
                    new_state.append((node_ind + 1, target_ind + 1))
                return new_state, match_attempt
        else:
            # If we're not at a wildcard, then make sure we haven't exhausted
            # nodes but not targets, since in this case one node can only match
            # one target
            if node_ind >= len(nodes) - 1 and target_ind < len(targets) - 1:
                return None

            match_attempt = node.matches(target)

            if match_attempt:
                return [(node_ind + 1, target_ind + 1)], match_attempt
            elif node == target:
                return [(node_ind + 1, target_ind + 1)], None
            else:
                return None

    @staticmethod
    def _matches_match_wilds(dictionary, wildcard_ind, nodes, targets):
        """Determine matches of a wildcard with sub-expression in `target`."""
        wildcard = nodes[wildcard_ind]
        begin, end = dictionary[wildcard_ind]
        terms = targets[begin:end + 1]
        # TODO: Should this be self.func?
        mul = Mul(*terms) if len(terms) > 1 else terms[0]
        return wildcard.matches(mul)

    @staticmethod
    def _matches_get_other_nodes(dictionary, nodes, node_ind):
        """Find other wildcards that may have already been matched."""
        other_node_inds = []
        for ind in dictionary:
            if nodes[ind] == nodes[node_ind]:
                other_node_inds.append(ind)
        return other_node_inds

    @staticmethod
    def _combine_inverse(lhs, rhs):
        """
        Returns lhs/rhs, but treats arguments like symbols, so things
        like oo/oo return 1 (instead of a nan) and ``I`` behaves like
        a symbol instead of sqrt(-1).
        """
        from .symbol import Dummy
        if lhs == rhs:
            return S.One

        def check(l, r):
            if l.is_Float and r.is_comparable:
                # if both objects are added to 0 they will share the same "normalization"
                # and are more likely to compare the same. Since Add(foo, 0) will not allow
                # the 0 to pass, we use __add__ directly.
                return l.__add__(0) == r.evalf().__add__(0)
            return False

        if check(lhs, rhs) or check(rhs, lhs):
            return S.One
        if any(i.is_Pow or i.is_Mul for i in (lhs, rhs)):
            # gruntz and limit wants a literal I to not combine
            # with a power of -1
            d = Dummy('I')
            _i = {S.ImaginaryUnit: d}
            i_ = {d: S.ImaginaryUnit}
            a = lhs.xreplace(_i).as_powers_dict()
            b = rhs.xreplace(_i).as_powers_dict()
            blen = len(b)
            for bi in tuple(b.keys()):
                if bi in a:
                    a[bi] -= b.pop(bi)
                    if not a[bi]:
                        a.pop(bi)
            if len(b) != blen:
                lhs = Mul(*[k ** v for k, v in a.items()]).xreplace(i_)
                rhs = Mul(*[k ** v for k, v in b.items()]).xreplace(i_)
        return lhs / rhs

    def as_powers_dict(self):
        d = defaultdict(int)
        for term in self.args:
            for b, e in term.as_powers_dict().items():
                d[b] += e
        return d

    def as_numer_denom(self):
        # don't use _from_args to rebuild the numerators and denominators
        # as the order is not guaranteed to be the same once they have
        # been separated from each other
        numers, denoms = list(zip(*[f.as_numer_denom() for f in self.args]))
        return self.func(*numers), self.func(*denoms)

    def as_base_exp(self):
        e1 = None
        bases = []
        nc = 0
        for m in self.args:
            b, e = m.as_base_exp()
#             if not b.is_commutative:
#                 nc += 1
            if e1 is None:
                e1 = e
            elif e != e1 or nc > 1:
                return self, S.One
            bases.append(b)
        return self.func(*bases), e1

    def _eval_is_polynomial(self, syms):
        return all(term._eval_is_polynomial(syms) for term in self.args)

    def _eval_is_rational_function(self, syms):
        return all(term._eval_is_rational_function(syms) for term in self.args)

    def _eval_is_meromorphic(self, x, a):
        return _fuzzy_group((arg.is_meromorphic(x, a) for arg in self.args),
                            quick_exit=True)

    def _eval_is_algebraic_expr(self, syms):
        return all(term._eval_is_algebraic_expr(syms) for term in self.args)

    def _eval_is_finite(self):
        if all(a.is_finite for a in self.args):
            return True
        if any(a.is_infinite for a in self.args):
            if all(a.is_zero == False for a in self.args):
                return False
            
    def _eval_is_algebraic(self):
        r = _fuzzy_group((a.is_algebraic for a in self.args), quick_exit=True)
        if r:
            return r
        elif r is False:
            return self.is_zero

    def _eval_is_zero(self):
        if self.shape:
            return
        zero = infinite = False
        for a in self.args:
            z = a.is_zero
            if z:
                if infinite:
                    return  # 0*oo is nan and nan.is_zero is None
                zero = True
            else:
                if not a.is_finite:
                    if zero:
                        return  # 0*oo is nan and nan.is_zero is None
                    infinite = True
                if zero is False and z is None:  # trap None
                    zero = None
        return zero

    def _eval_is_extended_integer(self):
        if all(arg.is_extended_integer for arg in self.args):
            return True
        
        is_rational = self.is_extended_rational

        if is_rational:
            n, d = self.as_numer_denom()
            if d is S.One:
                return True
            elif d is S(2):
                return n.is_even
        elif is_rational == False:
            return False

    def _eval_is_extended_rational(self):
        trues = []
        falses = []
        for arg in self.args:
            is_extended_rational = arg.is_extended_rational
            if is_extended_rational is None:
                return

            if is_extended_rational:
                trues.append(arg)
            else:
                falses.append(arg)

        if not trues:
            return False
        
        if not falses:
            return True
        
        for t in trues:
            is_zero = t.is_zero
            if is_zero:
                return True
            
            if is_zero is None:
                return

        return False

    def _eval_is_super_integer(self):
        return _fuzzy_group((a.is_super_integer for a in self.args), quick_exit=True)
        
    def _eval_is_hyper_rational(self):
        return _fuzzy_group((a.is_hyper_rational for a in self.args), quick_exit=True)
        
    def _eval_is_super_rational(self):
        return _fuzzy_group((a.is_super_rational for a in self.args), quick_exit=True)
    
    def _eval_is_extended_real(self):
        return self._eval_real_imag(True)

    def _eval_is_hyper_real(self):
        return _fuzzy_group((a.is_hyper_real for a in self.args), quick_exit=True)
        
    def _eval_is_super_real(self):
        return _fuzzy_group((a.is_super_real for a in self.args), quick_exit=True)

    def _eval_is_hyper_complex(self):
        return _fuzzy_group((a.is_hyper_complex for a in self.args), quick_exit=True)
    
    def _eval_is_extended_complex(self):
        return _fuzzy_group((a.is_extended_complex for a in self.args), quick_exit=True)

    def _eval_is_polar(self):
        has_polar = any(arg.is_polar for arg in self.args)
        return has_polar and all(arg.is_polar or arg.is_positive for arg in self.args)

    def _eval_real_imag(self, real):
        zero = False
        t_not_re_im = None

        for t in self.args:
            if t.is_complex == False and t.is_extended_real == False:
                return False
            elif t.is_imaginary:  # I
                real = not real
            elif t.is_extended_real:  # 2
                if not zero:
                    z = t.is_zero
                    if not z and zero == False:
                        zero = z
                    elif z:
                        if all(a.is_finite for a in self.args):
                            return True
                        return
            elif t.is_extended_real == False:
                # symbolic or literal like `2 + I` or symbolic imaginary
                if t_not_re_im:
                    return  # complex terms might cancel
                t_not_re_im = t
            elif t.is_imaginary == False:  # symbolic like `2` or `2 + I`
                if t_not_re_im:
                    return  # complex terms might cancel
                t_not_re_im = t
            else:
                return

        if t_not_re_im:
            if t_not_re_im.is_extended_real == False:
                if real:  # like 3
                    return zero  # 3*(smthng like 2 + I or i) is not real
            if t_not_re_im.is_imaginary == False:  # symbolic 2 or 2 + I
                if not real:  # like I
                    return zero  # I*(smthng like 2 or 2 + I) is not real
        elif zero == False:
            return real  # can't be trumped by 0
        elif real:
            return real  # doesn't matter what zero is

    def _eval_is_imaginary(self):
        z = self.is_zero
        if z:
            return False
        elif z == False:
            return self._eval_real_imag(False)

    def _eval_is_hermitian(self):
        return self._eval_herm_antiherm(True)

    def _eval_herm_antiherm(self, real):
        one_nc = zero = one_neither = False

        for t in self.args:
            if not t.is_commutative:
                if one_nc:
                    return
                one_nc = True

            if t.is_antihermitian:
                real = not real
            elif t.is_hermitian:
                if not zero:
                    z = t.is_zero
                    if not z and zero == False:
                        zero = z
                    elif z:
                        if all(a.is_finite for a in self.args):
                            return True
                        return
            elif t.is_hermitian == False:
                if one_neither:
                    return
                one_neither = True
            else:
                return

        if one_neither:
            if real:
                return zero
        elif zero == False or real:
            return real

    def _eval_is_antihermitian(self):
        z = self.is_zero
        if z:
            return False
        elif z == False:
            return self._eval_herm_antiherm(False)

    def _eval_is_irrational(self):
        for t in self.args:
            a = t.is_irrational
            if a:
                others = list(self.args)
                others.remove(t)
                if all((x.is_rational and fuzzy_not(x.is_zero)) is True for x in others):
                    return True
                return
            if a is None:
                return
        return False

    def _eval_is_extended_positive(self):
        """Return True if self is positive, False if not, and None if it
        cannot be determined.

        Explanation
        ===========

        This algorithm is non-recursive and works by keeping track of the
        sign which changes when a negative or nonpositive is encountered.
        Whether a nonpositive or nonnegative is seen is also tracked since
        the presence of these makes it impossible to return True, but
        possible to return False if the end result is nonpositive. e.g.

            pos * neg * nonpositive -> pos or zero -> None is returned
            pos * neg * nonnegative -> neg or zero -> False is returned
        """
        return self._eval_pos_neg(1)

    def _eval_pos_neg(self, sign):
        saw_NON = saw_NOT = False
        for t in self.args:
            if t.is_extended_positive:
                continue
            elif t.is_extended_negative:
                sign = -sign
            elif t.is_zero:
                if all(a.is_finite for a in self.args):
                    return False
                return
            elif t.is_extended_nonpositive:
                sign = -sign
                saw_NON = True
            elif t.is_extended_nonnegative:
                saw_NON = True
            elif t.is_extended_positive == False:
                sign = -sign
                if saw_NOT:
                    return
                saw_NOT = True
            elif t.is_extended_negative == False:
                if saw_NOT:
                    return
                saw_NOT = True
            else:
                return
        if sign == 1 and saw_NON is False and saw_NOT is False:
            return True
        if sign < 0:
            return False

    def _eval_is_extended_negative(self):
        return self._eval_pos_neg(-1)

    def _eval_is_even(self):
        is_integer = self.is_integer

        if is_integer:
            is_even = [t.is_even for t in self.args]
            if any(is_even):
                return True
            if all(b == False for b in is_even):
                return False
            return
        # !integer -> !odd
        if is_integer == False:
            return False

    def _eval_is_composite(self):
        """
        Here we count the number of arguments that have a minimum value
        greater than two.
        If there are more than one of such a symbol then the result is composite.
        Else, the result cannot be determined.
        """
        number_of_args = 0  # count of symbols with minimum value greater than one
        for arg in self.args:
            if not (arg.is_integer and arg.is_positive):
                return None
            if (arg - 1).is_positive:
                number_of_args += 1

        if number_of_args > 1:
            return True

    def _eval_is_singular(self):
        for arg in self.args:
            if arg.shape:
                is_singular = arg.is_singular
                if is_singular:
                    return True

                if is_singular is None:
                    return
                
            else:
                is_zero = arg.is_zero
                if is_zero:
                    return True
                
                if is_zero is None:
                    return
                
        return False

    def _eval_subs(self, old, new, **hint):
        if not old.is_Mul:
            return

        from sympy.functions.elementary.complexes import sign
        from sympy.ntheory.factor_ import multiplicity
        from sympy.simplify.powsimp import powdenest
        from sympy.simplify.radsimp import fraction

        # try keep replacement literal so -2*x doesn't replace 4*x
        if old.args[0].is_Number and old.args[0] < 0:
            if self.args[0].is_Number:
                if self.args[0] < 0:
                    return self._subs(-old, -new, **hint)
                return None

        def base_exp(a):
            # if I and -1 are in a Mul, they get both end up with
            # a -1 base (see issue 6421); all we want here are the
            # true Pow or exp separated into base and exponent
            from sympy import exp
            if a.is_Pow or isinstance(a, exp):
                return a.as_base_exp()
            return a, S.One

        def breakup(eq):
            """break up powers of eq when treated as a Mul:
                   b**(Rational*e) -> b**e, Rational
                commutatives come back as a dictionary {b**e: Rational}
                noncommutatives come back as a list [(b**e, Rational)]
            """

            (c, nc) = (defaultdict(int), list())
            for a in Mul.make_args(eq):
                a = powdenest(a)
                (b, e) = base_exp(a)
                if e is not S.One:
                    (co, _) = e.as_coeff_mul()
                    b = Pow(b, e / co)
                    e = co
#                 if a.is_commutative:
                c[b] += e
#                 else:
#                     nc.append([b, e])
            return (c, nc)

        def rejoin(b, co):
            """
            Put rational back with exponent; in general this is not ok, but
            since we took it from the exponent for analysis, it's ok to put
            it back.
            """

            (b, e) = base_exp(b)
            return Pow(b, e * co)

        def ndiv(a, b):
            """if b divides a in an extractive way (like 1/4 divides 1/2
            but not vice versa, and 2/5 does not divide 1/3) then return
            the integer number of times it divides, else return 0.
            """
            if not b.q % a.q or not a.q % b.q:
                return int(a / b)
            return 0

        # give Muls in the denominator a chance to be changed (see issue 5651)
        # rv will be the default return value
        rv = None
        n, d = fraction(self)
        self2 = self
        if d is not S.One:
            self2 = n._subs(old, new, **hint) / d._subs(old, new, **hint)
            if not self2.is_Mul:
                return self2._subs(old, new, **hint)
            if self2 != self:
                rv = self2

        # Now continue with regular substitution.

        # handle the leading coefficient and use it to decide if anything
        # should even be started; we always know where to find the Rational
        # so it's a quick test

        co_self = self2.args[0]
        co_old = old.args[0]
        co_xmul = None
        if co_old.is_Rational and co_self.is_Rational:
            # if coeffs are the same there will be no updating to do
            # below after breakup() step; so skip (and keep co_xmul=None)
            if co_old != co_self:
                co_xmul = co_self.extract_multiplicatively(co_old)
        elif co_old.is_Rational:
            return rv

        # break self and old into factors

        (c, nc) = breakup(self2)
        (old_c, old_nc) = breakup(old)

        # update the coefficients if we had an extraction
        # e.g. if co_self were 2*(3/35*x)**2 and co_old = 3/5
        # then co_self in c is replaced by (3/5)**2 and co_residual
        # is 2*(1/7)**2

        if co_xmul and co_xmul.is_Rational and abs(co_old) != 1:
            mult = S(multiplicity(abs(co_old), co_self))
            c.pop(co_self)
            if co_old in c:
                c[co_old] += mult
            else:
                c[co_old] = mult
            co_residual = co_self / co_old ** mult
        else:
            co_residual = S.One

        # do quick tests to see if we can't succeed

        ok = True
        if len(old_nc) > len(nc):
            # more non-commutative terms
            ok = False
        elif len(old_c) > len(c):
            # more commutative terms
            ok = False
        elif {i[0] for i in old_nc}.difference({i[0] for i in nc}):
            # unmatched non-commutative bases
            ok = False
        elif set(old_c).difference(set(c)):
            # unmatched commutative terms
            ok = False
        elif any(sign(c[b]) != sign(old_c[b]) for b in old_c):
            # differences in sign
            ok = False
        if not ok:
            return rv

        if not old_c:
            cdid = None
        else:
            rat = []
            for (b, old_e) in old_c.items():
                c_e = c[b]
                rat.append(ndiv(c_e, old_e))
                if not rat[-1]:
                    return rv
            cdid = min(rat)

        if not old_nc:
            ncdid = None
            for i in range(len(nc)):
                nc[i] = rejoin(*nc[i])
        else:
            ncdid = 0  # number of nc replacements we did
            take = len(old_nc)  # how much to look at each time
            limit = cdid or S.Infinity  # max number that we can take
            failed = []  # failed terms will need subs if other terms pass
            i = 0
            while limit and i + take <= len(nc):
                hit = False

                # the bases must be equivalent in succession, and
                # the powers must be extractively compatible on the
                # first and last factor but equal in between.

                rat = []
                for j in range(take):
                    if nc[i + j][0] != old_nc[j][0]:
                        break
                    elif j == 0:
                        rat.append(ndiv(nc[i + j][1], old_nc[j][1]))
                    elif j == take - 1:
                        rat.append(ndiv(nc[i + j][1], old_nc[j][1]))
                    elif nc[i + j][1] != old_nc[j][1]:
                        break
                    else:
                        rat.append(1)
                    j += 1
                else:
                    ndo = min(rat)
                    if ndo:
                        if take == 1:
                            if cdid:
                                ndo = min(cdid, ndo)
                            nc[i] = Pow(new, ndo) * rejoin(nc[i][0],
                                    nc[i][1] - ndo * old_nc[0][1])
                        else:
                            ndo = 1

                            # the left residual

                            l = rejoin(nc[i][0], nc[i][1] - ndo * 
                                    old_nc[0][1])

                            # eliminate all middle terms

                            mid = new

                            # the right residual (which may be the same as the middle if take == 2)

                            ir = i + take - 1
                            r = (nc[ir][0], nc[ir][1] - ndo * 
                                 old_nc[-1][1])
                            if r[1]:
                                if i + take < len(nc):
                                    nc[i:i + take] = [l * mid, r]
                                else:
                                    r = rejoin(*r)
                                    nc[i:i + take] = [l * mid * r]
                            else:

                                # there was nothing left on the right

                                nc[i:i + take] = [l * mid]

                        limit -= ndo
                        ncdid += ndo
                        hit = True
                if not hit:

                    # do the subs on this failing factor

                    failed.append(i)
                i += 1
            else:

                if not ncdid:
                    return rv

                # although we didn't fail, certain nc terms may have
                # failed so we rebuild them after attempting a partial
                # subs on them

                failed.extend(range(i, len(nc)))
                for i in failed:
                    nc[i] = rejoin(*nc[i])._subs(old, new, **hint)

        # rebuild the expression

        if cdid is None:
            do = ncdid
        elif ncdid is None:
            do = cdid
        else:
            do = min(ncdid, cdid)

        margs = []
        for b in c:
            if b in old_c:

                # calculate the new exponent

                e = c[b] - old_c[b] * do
                margs.append(rejoin(b, e))
            else:
                margs.append(rejoin(b._subs(old, new, **hint), c[b]))
        if cdid and not ncdid:

            # in case we are replacing commutative with non-commutative,
            # we want the new term to come at the front just like the
            # rest of this routine

            margs = [Pow(new, cdid)] + margs

        prod = co_residual
        for m in margs:
            prod *= m

        for m in nc:
            prod *= m
            
        return prod

    def _eval_nseries(self, x, n, logx):
        from sympy import Order, powsimp
        terms = [t.nseries(x, n=n, logx=logx) for t in self.args]
        res = powsimp(self.func(*terms).expand(), combine='exp', deep=True)
        if res.has(Order):
            res += Order(x ** n, x)
        return res

    def _eval_as_leading_term(self, x, cdir=0):
        return self.func(*(t.as_leading_term(x, cdir=cdir) for t in self.args))

    def _eval_conjugate(self):
        return self.func(*(t.conjugate() for t in self.args))

    def _eval_adjoint(self):
        return self.func(*(t.adjoint() for t in self.args[::-1]))

    def _eval_exp(self):
        from sympy import logcombine, log
        if self.is_number or self.is_Symbol:
            coeff = self.coeff(S.Pi * S.ImaginaryUnit)
            if coeff:
                if coeff.is_even:
                    return S.One
                if coeff.is_odd:
                    return S.NegativeOne
                coeff += S.Half
                if coeff.is_even:
                    return -S.ImaginaryUnit
                if coeff.is_odd:
                    return S.ImaginaryUnit

        # Warning: code in risch.py will be very sensitive to changes
        # in this (see DifferentialExtension).

        # look for a single log factor

        coeff, terms = self.as_coeff_Mul()

        # but it can't be multiplied by oo
        if coeff.is_NegativeInfinity:
            from sympy.matrices.expressions.matexpr import ZeroMatrix
            if terms.is_extended_positive or terms.is_extended_negative:
                return ZeroMatrix(*terms.shape)
            return
        elif coeff.is_Infinity:
            return

        coeffs, log_term = [coeff], None
        for term in Mul.make_args(terms):
            term_ = logcombine(term)
            if isinstance(term_, log):
                if log_term is None:
                    log_term = term_.args[0]
                else:
                    return None
            elif term.is_comparable or term.is_negative or term.is_positive:
                coeffs.append(term)
            else:
                return None

        return log_term ** Mul(*coeffs) if log_term else None

    def _sage_(self):
        s = 1
        for x in self.args:
            s *= x._sage_()
        return s

    def as_content_primitive(self, radical=False, clear=True):
        """Return the tuple (R, self/R) where R is the positive Rational
        extracted from self.

        Examples
        ========

        >>> from sympy import sqrt
        >>> (-3*sqrt(2)*(2 - 2*sqrt(2))).as_content_primitive()
        (6, -sqrt(2)*(1 - sqrt(2)))

        See docstring of Expr.as_content_primitive for more examples.
        """

        coef = S.One
        args = []
        for i, a in enumerate(self.args):
            c, p = a.as_content_primitive(radical=radical, clear=clear)
            coef *= c
            if p is not S.One:
                args.append(p)
        # don't use self._from_args here to reconstruct args
        # since there may be identical args now that should be combined
        # e.g. (2+2*x)*(3+3*x) should be (6, (1 + x)**2) not (6, (1+x)*(1+x))
        return coef, self.func(*args)

    def as_ordered_factors(self, order=None):
        """Transform an expression into an ordered list of factors.

        Examples
        ========

        >>> from sympy import sin, cos
        >>> from sympy.abc import x, y

        >>> (2*x*y*sin(x)*cos(x)).as_ordered_factors()
        [2, x, y, sin(x), cos(x)]

        """
        cpart, ncpart = self.args_cnc()
        cpart.sort(key=lambda expr: expr.sort_key(order=order))
        return cpart + ncpart

    @property
    def _sorted_args(self):
        return tuple(self.as_ordered_factors())

    def as_coeff_mmul(self):
        return 1, self

    @classmethod
    def simplify_Equal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a Mul object!
        """
        if rhs.is_Mul:
            lhs_args = [*lhs.args]
            rhs_args = [*rhs.args]
            intersect = set(lhs_args) & set(rhs_args)
            if intersect:
                hit = False
                for arg in intersect:
                    if arg.is_nonzero:
                        lhs_args.remove(arg)
                        rhs_args.remove(arg)
                        hit = True
                if hit:
                    return self.func(cls(*lhs_args), cls(*rhs_args)).simplify()
        elif rhs.is_zero:
            return Basic.simplify_Equal(self, lhs, rhs)

    def simplify_KroneckerDelta(self):
        for arg in self.args:
            if arg.is_KroneckerDelta:
                i, j = arg.args
                if i == 0 and j in self.args or j == 0 and i in self.args:
                    return S.Zero

        coefficient = []
        delta = []
        for i, arg in enumerate(self.args):
            if {*arg.enumerate_KroneckerDelta()}:
                delta.append(arg)
            else:
                coefficient.append(arg)
        if not delta: 
            return self
        
        if len(delta) == 1: 
            return self

        delta = self.func(*delta, evaluate=False).expand()
        
        if coefficient: 
            coefficient = self.func(*coefficient, evaluate=False)
        else:
            coefficient = S.One
             
        this = delta
        if this.is_Add:
            args = [*this.args]
            hit = False
            for i, arg in enumerate(this.args):
                if arg.is_Mul:
                    _arg = arg.simplify_KroneckerDelta()
                    if arg != _arg:
                        args[i] = _arg
                        hit = True
            if hit:
                this = this.func(*args)
            if this.is_Add:
                this = this.simplify_KroneckerDelta()
            if this != delta:
                return this * coefficient
        else:
            this *= coefficient
            if this != self:
                return this
            
        return self
    
    @staticmethod
    def can_be_canceled(expr, a):
        if expr.is_Pow:
            _a, e = expr.args
            if e == -1:
                if _a == a or a == -a:
                    return True
        elif expr.is_Rational:
            q = expr.q
            if q == a or q == -a:
                return True

    def simplify(self, deep=False, **kwargs):
        if deep:
            return Expr.simplify(self, deep=True, **kwargs)
        
        for i, arg in enumerate(self.args):
            if arg.is_Lamda:
                _arg = arg.simplify(squeeze=True)
                if _arg != arg:
                    args = [*self.args]
                    args[i] = _arg
                    return self.func(*args).simplify()
            elif arg.is_Pow:
                b, e = arg.args
                if e is S.NegativeOne:
                    try:
                        j = self.args.index(-b)
                        args = [*self.args]
                        args[i] = -1
                        del args[j]
                        return self.func(*args).simplify()
                    except:
                        ...
                        
        a = self.args[0]
        # dissolve the initial minus sign
        if a.is_Number and a._coeff_isneg():
            b = self.args[1]
            if b.is_Add:
                if a.is_infinite:
                    return self.func(*(-a, b.func(*(-arg for arg in b.args))) + self.args[2:])
                else:
                    if b.args[0]._coeff_isneg():
                        return self.func(*(b.func(*(arg * a for arg in b.args)),) + self.args[2:])
                    
                    for arg in b.args:
                        if arg.is_Mul:
                            if any(self.can_be_canceled(arg, a) for arg in arg.args):
                                hit = True
                                break

                        elif self.can_be_canceled(arg, a):
                            hit = True
                            break

                    else:
                        hit = False
                        
                    if hit:
                        return self.func(*(b.func(*(arg * a for arg in b.args)),) + self.args[2:])
                                            

        infinity = []
        coeff = []
        for arg in self.args:
            if arg == S.Infinity or arg == S.NegativeInfinity:
                infinity.append(arg)
            else:
                coeff.append(arg)

        if infinity:
            positive = True
            for inf in infinity:
                if inf == S.NegativeInfinity:
                    positive = not positive

            coeff = Mul(*coeff)
            if coeff > 0:
                return S.Infinity if positive else S.NegativeInfinity
            elif coeff < 0:
                return S.NegativeInfinity if positive else S.Infinity

        from sympy import KroneckerDelta
        if self._has(KroneckerDelta):
            this = self.simplify_KroneckerDelta()
            if this != self:
                return this
            
        this = self.simplifyProduct()
        if this is not self:
            return this
        
        pows = {}
        nonpows = []
        hit = False
        for arg in self.args:
            if arg.is_Pow:
                b, e = arg.args
                if b in pows:
                    pows[b] += e
                    hit = True
                else:
                    pows[b] = e
            else:
                nonpows.append(arg)
                
        if hit:
            return self.func(*[b ** e for b, e in pows.items()]) * self.func(*nonpows)
        return self

    def simplifyProduct(self):
        
        dic = {}
        coeffs = []
        for arg in self.args:

            if arg.is_Product:
                if S.One in dic:
                    dic[S.One].append(arg)
                else:
                    dic[S.One] = [arg]
                continue
            coeffs.append(arg)

        hit = False
        
        for coeff in dic:
            if self.prod_result(dic[coeff]):
                hit = True

        if hit:
            arr = []
            for coeff, expr in dic.items():
                arr += [n ** coeff for n in expr]
            return self.func(*arr + coeffs).simplify()
        
        return self

    def prod_result(self, positive):
        from sympy.concrete.expr_with_limits import limits_empty
        for i in range(len(positive)):
            for j in range(i + 1, len(positive)):
                if not positive[i].is_Product or not positive[j].is_Product:
                    continue
                if positive[i].expr == positive[j].expr:
                    limits = positive[i].limits_intersect(positive[j])
                    if not limits_empty(limits):
                        if positive[i].limits == positive[j].limits:
                            positive[i] *= 2
                            del positive[j]
                            return True
                        continue
                    limits = positive[i].limits_union(positive[j])
                    positive[i] = positive[i].func(positive[i].expr, *limits)
                    del positive[j]
                    return True

    def _eval_transpose(self, axis=-1):
        if axis == self.default_axis:
            scalar = []
            vector = []
            matrix = []
            for arg in self.args:
                if not arg.shape:
                    scalar.append(arg)
                elif len(arg.shape) == 1:
                    vector.append(arg)
                else:
                    matrix.append(arg)
                
            if not vector:
                return self.func(*(arg.T for arg in self.args))

            if scalar:
                return self.func(*vector, *matrix).T * self.func(*scalar)
            
            if len(matrix) == 1:
                matrix, = matrix
                if matrix.is_Identity:
                    return self

    def domain_nonzero(self, x):
        from sympy.core.numbers import oo
        domain = x.range(-oo, oo)
        for arg in self.args:
            domain &= arg.domain_nonzero(x)
        return domain

    def as_coeff_Sum(self):
        from sympy.concrete import summations

        summation = None
        i = -1
        for index, arg in enumerate(self.args):
            if isinstance(arg, summations.Sum):
                summation = arg
                i = index

        if summation is None:
            return None, None
        args = self.args[:i] + self.args[i + 1:]

        return self.func(*args), summation

    @property
    def domain(self): 
        if self.is_integer:
            from sympy.sets import Integers
            domain = Integers
        elif self.is_real:
            from sympy.sets.fancysets import Reals
            domain = Reals
        elif self.is_extended_real:
            from sympy.sets.fancysets import ExtendedReals
            domain = ExtendedReals
        elif self.is_complex:
            domain = S.Complexes
        elif self.is_extended_complex:
            domain = S.ExtendedComplexes
        elif self.is_super_real:
            from sympy import SuperReals
            domain = SuperReals
        else:
            from sympy import SuperComplexes
            domain = SuperComplexes
            
        coeff = []
        
        max_shape_len = max(len(arg.shape) for arg in self.args)
        if max_shape_len:
            from sympy.sets.sets import CartesianSpace
            domain = CartesianSpace(domain, *self.shape)
            return domain
    
        if all(len(arg.shape) == max_shape_len for arg in self.args):
            for arg in self.args:
                if arg.is_number:
                    coeff.append(arg)
                    continue
#                 domain *= arg.domain
            if coeff:
                if domain:
                    return domain * Mul(*coeff)
                return domain
        else:
            for arg in self.args:
                if len(arg.shape) < max_shape_len:
                    coeff.append(arg)
                    continue
#                 domain *= arg.domain
            
            if coeff: 
                return domain * Mul(*coeff).domain

        return domain

    def __iter__(self):
        raise TypeError
    
    __getitem__ = AssocOp.getitem
    
    def _latex(self, p):
        from sympy.core.power import Pow
        include_parens = False
        if self._coeff_isneg():
            self = -self
            tex = "- "
            if self.is_Add:
                tex += "("
                include_parens = True
        else:
            tex = ""

        from sympy.simplify import fraction
        numer, denom = fraction(self, exact=True)
        separator = p._settings['mul_symbol_latex']
        numbersep = p._settings['mul_symbol_latex_numbers']

        def convert(expr):
            from sympy.printing.latex import _between_two_numbers_p
            if not expr.is_Mul:
                return str(p._print(expr))
            else:
                _tex = last_term_tex = ""

                if p.order not in ('old', 'none'):
                    args = expr.as_ordered_factors()
                else:
                    args = list(expr.args)

                # If quantities are present append them at the back
                args = sorted(args, key=lambda x: x.is_Quantity is True or (isinstance(x, Pow) and x.base.is_Quantity is True))

                for i, term in enumerate(args):
                    term_tex = p._print(term)

                    if not term.is_Product and not term.is_Bool and not term.is_Exp and p._needs_mul_brackets(term, first=(i == 0), last=(i == len(args) - 1)) or term.is_Reduced and i < len(args) - 1:
                        term_tex = r"\left(%s\right)" % term_tex

                    if _between_two_numbers_p[0].search(last_term_tex) and _between_two_numbers_p[1].match(term_tex):
                        # between two numbers
                        _tex += numbersep
                    elif _tex:
                        prev = args[i - 1]
                        if prev.is_OneMatrix or \
                        term.is_OneMatrix or \
                        (prev.is_Atom or prev.is_Lamda) and (term.is_Lamda or term.is_Mod) or \
                        prev.is_Product and term.is_ExprWithLimits:
                            _tex += " \cdot "
                        else:
                            _tex += separator

                    _tex += term_tex
                    last_term_tex = term_tex
                return _tex

        if denom is S.One and Pow(1, -1, evaluate=False) not in self.args:
            # use the original expression here, since fraction() may have
            # altered it when producing numer and denom
            tex += convert(self)

        else:
            snumer = convert(numer)
            sdenom = convert(denom)
            ldenom = len(sdenom.split())
            ratio = p._settings['long_frac_ratio']
            if p._settings['fold_short_frac'] and ldenom <= 2 and "^" not in sdenom:
                # handle short fractions
                if p._needs_mul_brackets(numer, last=False):
                    tex += r"\left(%s\right) / %s" % (snumer, sdenom)
                else:
                    tex += r"%s / %s" % (snumer, sdenom)
            elif ratio is not None and len(snumer.split()) > ratio * ldenom:
                # handle long fractions
                if p._needs_mul_brackets(numer, last=True):
                    tex += r"\frac{1}{%s}%s\left(%s\right)" % (sdenom, separator, snumer)
#                     tex += r"\displaystyle\frac{1}{%s}%s\left(%s\right)" % (sdenom, separator, snumer)
                elif numer.is_Mul:
                    # split a long numerator
                    a = S.One
                    b = S.One
                    for x in numer.args:
                        if p._needs_mul_brackets(x, last=False) or len(convert(a * x).split()) > ratio * ldenom or (b.is_commutative is x.is_commutative == False):
                            b *= x
                        else:
                            a *= x
                    if p._needs_mul_brackets(b, last=True):
                        tex += r"\frac{%s}{%s}%s\left(%s\right)" % (convert(a), sdenom, separator, convert(b))
                    else:
                        tex += r"\frac{%s}{%s}%s%s" % (convert(a), sdenom, separator, convert(b))
                else:
                    tex += r"\frac{1}{%s}%s%s" % (sdenom, separator, snumer)
            else:
                tex += r"\frac{%s}{%s}" % (snumer, sdenom)

        if include_parens:
            tex += ")"
        return tex
    
    def _sympystr(self, p):
        from sympy.printing.precedence import precedence
        prec = precedence(self)

        c, e = self.as_coeff_Mul()
        if c < 0:
            self = _keep_coeff(-c, e)
            sign = "-"
        else:
            sign = ""

        a = []  # items in the numerator
        b = []  # items that are in the denominator (if any)

        pow_paren = []  # Will collect all pow with more than one base element and exp = -1

        if p.order not in ('old', 'none'):
            args = self.as_ordered_factors()
        else:
            # use make_args in case self was something like -x -> x
            args = Mul.make_args(self)

        # Gather args for numerator/denominator
        for item in args:
#             if item.is_commutative and item.is_Pow and item.exp.is_Rational and item.exp.is_negative:
            if item.is_Pow and item.exp.is_Rational and item.exp.is_negative:
                if item.exp != -1:
                    b.append(Pow(item.base, -item.exp, evaluate=False))
                else:
                    if len(item.args[0].args) != 1 and isinstance(item.base, Mul):  # To avoid situations like #14160
                        pow_paren.append(item)
                    b.append(Pow(item.base, -item.exp))
            elif item.is_Rational and item is not S.Infinity:
                if item.p != 1:
                    a.append(Rational(item.p))
                if item.q != 1:
                    b.append(Rational(item.q))
            else:
                a.append(item)

        a = a or [S.One]

        a_str = [p.parenthesize(x, prec, strict=False) for x in a]
        b_str = [p.parenthesize(x, prec, strict=False) for x in b]

        # To parenthesize Pow with exp = -1 and having more than one Symbol
        for item in pow_paren:
            if item.base in b:
                b_str[b.index(item.base)] = "(%s)" % b_str[b.index(item.base)]

        if len(a) > 1:
            if a[0].is_DenseMatrix or a[0].is_BlockMatrix and a[0].axis == 0:
                if a[1].is_DenseMatrix or a[1].is_BlockMatrix:
                    #sympify the first element
                    a_str[0] = 'S' + a_str[0]

        if not b:
            return sign + ' * '.join(a_str)

        if len(b) == 1:
            return sign + ' * '.join(a_str) + " / " + b_str[0]

        return sign + ' * '.join(a_str) + " / (%s)" % '*'.join(b_str)

    def _pretty(self, p):
        from sympy.printing.pretty.stringpict import prettyForm
        a = []  # items in the numerator
        b = []  # items that are in the denominator (if any)

        if p.order not in ('old', 'none'):
            try:
                args = self.as_ordered_factors()
            except TypeError:
                args = list(self.args)
        else:
            args = list(self.args)

        # If quantities are present append them at the back
        args = sorted(args, key=lambda x: x.is_Quantity or
                     (isinstance(x, Pow) and x.base.is_Quantity))

        # Gather terms for numerator/denominator
        for item in args:
            if item.is_Pow and item.exp.is_Rational and item.exp.is_negative:
                if item.exp != -1:
                    b.append(Pow(item.base, -item.exp, evaluate=False))
                else:
                    b.append(Pow(item.base, -item.exp))
            elif item.is_Rational and item is not S.Infinity:
                if item.p != 1:
                    a.append(Rational(item.p))
                if item.q != 1:
                    b.append(Rational(item.q))
            else:
                a.append(item)

        from sympy import Integral, Piecewise, Product, Sum

        # Convert to pretty forms. Add parens to Add instances if there
        # is more than one term in the numer/denom
        for i in range(0, len(a)):
            if (a[i].is_Add and len(a) > 1) or (i != len(a) - 1 and
                    isinstance(a[i], (Integral, Piecewise, Product, Sum))):
                a[i] = prettyForm(*p._print(a[i]).parens())
            elif a[i].is_Relational:
                a[i] = prettyForm(*p._print(a[i]).parens())
            else:
                a[i] = p._print(a[i])

        for i in range(0, len(b)):
            if (b[i].is_Add and len(b) > 1) or (i != len(b) - 1 and
                    isinstance(b[i], (Integral, Piecewise, Product, Sum))):
                b[i] = prettyForm(*p._print(b[i]).parens())
            else:
                b[i] = p._print(b[i])

        # Construct a pretty form
        if len(b) == 0:
            return prettyForm.__mul__(*a)
        else:
            if len(a) == 0:
                a.append(p._print(S.One))
            return prettyForm.__mul__(*a) / prettyForm.__mul__(*b)

    @property
    def is_lower(self):
        for arg in self.args:
            if not arg.shape:
                continue
            if len(arg.shape) == 1:
                continue
            if arg.is_lower:
                continue
            return False
        return True
             
    @property
    def is_upper(self):
        for arg in self.args:
            if not arg.shape:
                continue
            if len(arg.shape) == 1:
                continue
            if arg.is_upper:
                continue
            return False
        return True

    def enumerate_KroneckerDelta(self):
        for arg in self.args:
            yield from arg.enumerate_KroneckerDelta()

    def _eval_inverse(self):
        return self.func(*[arg.inverse() for arg in self.args])        

    def _eval_Abs(self):
        from sympy import signsimp, Abs
        arg = signsimp(self, evaluate=False)
        known = []
        unk = []
        for t in arg.args:
            tnew = Abs(t)
            if isinstance(tnew, Abs) and tnew.arg == t:
                unk.append(tnew.args[0])
            else:
                known.append(tnew)
        known = Mul(*known)
        unk = Abs(Mul(*unk), evaluate=False) if unk else S.One
        return known * unk
    
    @property
    def dtype(self):
        if self.is_integer:
            from sympy import dtype
            return dtype.integer
        return super(Mul, self).dtype

    def squeeze(self):
        return self.func(*[t for t in self.args if not t.is_OneMatrix])

    def of(self, cls, **kwargs):
        from sympy.core.of import Basic
        if isinstance(cls, Basic):
            indices = kwargs.get('indices', [None] * len(cls.args))
            res = Expr.of(self, cls, indices=indices)
        else:
            res = Expr.of(self, cls)
            indices = []

        if res is None:
            if cls.is_Mul:
                return self.rotary_match(cls, indices)
            
            elif cls.is_Pow:
                if len(cls.args) == 2 and cls.args[1] in (-1, 2):
                    b, e = cls.args
                    if b.is_Mul:
                        if len(b.args) == len(self.args):
                            cls = [b ** e for b in b.args]
                            args = []
                            for cls, arg in zip(cls, self.args):
                                arg = arg.of(cls)
                                if arg is None:
                                    break
                                args.append(arg)
                            else:
                                return tuple(args)
                        else:
                            return
                    args = []
                    for arg in self.args:
                        arg = arg.of(cls)
                        if arg is None:
                            break
                        args.append(arg)
                    else:
                        return Mul(*args)
                     
        elif isinstance(res, tuple):
            if cls.is_Mul:
                if not isinstance(cls, type):
                    try:
                        if cls.of_LinearPattern():
                            return Mul(*res)
                        
                        if len(cls.args) == 2:
                            if len(res) > 2:
                                a, b = cls.args
                                if a is Expr and (b is not Expr):
                                    index = indices[1]
                                    b = res[index]
                                    res = res[:index] + res[index + 1:]
                                    a = Mul(*res)
                                    return a, b
                        elif len(cls.args) == 1:
                            for i, r in enumerate(res):
                                if isinstance(r, tuple):
                                    first = res[i]
                                    rest = res[:i] + res[i + 1:]
                                    res = (first, *rest)  
                                    break
                                              
                    except AttributeError:
                        cls = Basic.__new__(Mul, *cls.args)
                        if cls.of_LinearPattern():
                            return Mul(*res)
                    
        return res

    def of_simple_poly(self, x):
        '''
        extract the coefficients of a simple polynomial
        (a * x + b).of_simple_poly(x) = [b, a]
        '''
        B = None
        A = None
        
        for arg in self.args:
            b, a = arg.of_simple_poly(x)
            if b is None:
                break
            
            if B is None:
                B = b
                A = a
            else:
                if a:
                    if A:
                        return None, None
#                     previously, f(x) = B, it becomes B * (x * a + b) = x * aB + bB
                    A = a * B
                    B *= b
                else:
                    B *= b
                    A *= b
            
        return B, A
    
    def monotonicity(self, x):
        factor = 1
        monotonicity = None
        [*args] = self.args
        
        for i, arg in enumerate(args):
            if arg._has(x):
                if monotonicity is None:
                    args[i], monotonicity = arg.monotonicity(x)
                    if not monotonicity:
                        if isinstance(args[i], tuple):
                            lower, upper = args[i]
                            if factor < 0:
                                lower, upper = upper, lower
                            [*args] = self.args
                            args[i] = lower
                            
                            lower = Mul(*args)
                            expr_lower, mon_lower = lower.monotonicity(x)
                            
                            args[i] = upper
                            upper = Mul(*args)
                            expr_upper, mon_upper = upper.monotonicity(x)

                            if mon_lower < 0:
                                if mon_upper > 0:
                                    ...
                                elif mon_upper < 0:
                                    ...
                                else:
                                    if not upper._has(x):
                                        return (expr_lower, upper), 0
                            elif mon_lower > 0:
                                ...
                            else:
                                if mon_upper > 0:
                                    ...
                                elif mon_upper < 0:
                                    ...
                                else:
                                    if not lower._has(x):
                                        if not upper._has(x):
                                            return (lower, upper), 0                            
                        return None, 0
                else:
                    return None, 0
            else:
                if arg > 0:
                    ...
                elif arg < 0:
                    factor *= -1
                else:
                    return None, 0
                
        if monotonicity is None:
            return None, 0

        return self.func(*args, evaluate=False), monotonicity * factor
    
    def is_continuous_at(self, *args):
        from sympy.core.logic import fuzzy_and
        return fuzzy_and(x.is_continuous_at(*args) for x in self.args)

    def _eval_torch(self):
        return prod(arg.torch for arg in self.args)

    @staticmethod
    def simplify_Lamda(self, squeeze=False):
        vars = self.variables
        limits = self.limits
        modified = []
        deformed = []
        unmodified = []
        constants = []
        for arg in self.expr.args:
            if arg.has(*vars):
                if arg.is_Add:
                    unmodified.append(arg)
                else:
                    lamda = self.func(arg, *limits)
                    _lamda = lamda.simplify()
                    if _lamda != lamda:
                        if len(_lamda.shape) < len(self.shape):
                            deformed.append(_lamda)
                        else:
                            modified.append(_lamda)
                    else:
                        unmodified.append(arg)
            else:
                constants.append(arg)
    
        if deformed or modified or constants:
            
            if unmodified:
                if max(len(expr.shape) for expr in unmodified) < len(self.expr.shape):
                    from sympy import OneMatrix
                    one = OneMatrix(*self.expr.shape)
                    try:
                        del constants[constants.index(one)]
                        if not constants and not modified:
                            return self
                        
                    except ValueError:
                        ...
                        
                    unmodified.append(one)
                    
                unmodified = self.func(Mul(*unmodified), *limits)
                unmodified = [unmodified]

            if deformed:
                deformed = Mul(*deformed)
                from sympy import Transpose
                deformed = Transpose.expand_dims(deformed, self.shape, len(self.limits))
                deformed = [deformed]

            return Mul(*constants, *modified, *unmodified, *deformed)
        
        return self
    
    @cacheit
    def sort_key(self, order=None):
        coeff, expr = self.as_coeff_Mul()

        if expr.is_Pow:
            expr, exp = expr.args
        else:
            expr, exp = expr, S.One

        if expr.is_Dummy:
            args = (expr.sort_key(),)
        elif expr.is_Atom:
            args = (str(expr),)
        else:
            if expr.is_Add:
                args = expr.as_ordered_terms(order=order)
            elif expr.is_Mul:
                args = expr.as_ordered_factors(order=order)
            else:
                args = expr.args

            args = tuple(arg.sort_key(order=order) for arg in args)

        args = len(args), tuple(arg.class_key() for arg in self.args), args
        exp = exp.sort_key(order=order)

        class_key = expr.class_key()
        return (*class_key, *coeff.sort_key()), args, exp, coeff


mul = AssocOpDispatcher('mul')

    
def prod(a, start=1):
    """Return product of elements of a. Start with int 1 so if only
       ints are included then an int result is returned.

    Examples
    ========

    >>> from sympy import prod, S
    >>> prod(range(3))
    0
    >>> type(_) is int
    True
    >>> prod([S(2), 3])
    6
    >>> _.is_Integer
    True

    You can start the product at something other than 1:

    >>> prod([1, 2], 3)
    6

    """
    return reduce(operator.mul, a, start)


def _keep_coeff(coeff, factors, clear=True, sign=False):
    """Return ``coeff*factors`` unevaluated if necessary.

    If ``clear`` is False, do not keep the coefficient as a factor
    if it can be distributed on a single factor such that one or
    more terms will still have integer coefficients.

    If ``sign`` is True, allow a coefficient of -1 to remain factored out.

    Examples
    ========

    >>> from sympy.core.mul import _keep_coeff
    >>> from sympy.abc import x, y
    >>> from sympy import S

    >>> _keep_coeff(S.Half, x + 2)
    (x + 2)/2
    >>> _keep_coeff(S.Half, x + 2, clear=False)
    x/2 + 1
    >>> _keep_coeff(S.Half, (x + 2)*y, clear=False)
    y*(x + 2)/2
    >>> _keep_coeff(S(-1), x + y)
    -x - y
    >>> _keep_coeff(S(-1), x + y, sign=True)
    -(x + y)
    """

    if not coeff.is_Number:
        if factors.is_Number:
            factors, coeff = coeff, factors
        else:
            return coeff * factors
    if coeff is S.One:
        return factors
    elif coeff is S.NegativeOne and not sign:
        return -factors
    elif factors.is_Add:
        if not clear and coeff.is_Rational and coeff.q != 1:
            q = S(coeff.q)
            for i in factors.args:
                c, t = i.as_coeff_Mul()
                r = c / q
                if r == int(r):
                    return coeff * factors
        return Mul(coeff, factors, evaluate=False)
    elif factors.is_Mul:
        margs = list(factors.args)
        if margs[0].is_Number:
            margs[0] *= coeff
            if margs[0] == 1:
                margs.pop(0)
        else:
            margs.insert(0, coeff)
        return Mul._from_args(margs)
    else:
        return coeff * factors


def expand_2arg(e):
    from sympy.simplify.simplify import bottom_up

    def do(e):
        if e.is_Mul:
            c, r = e.as_coeff_Mul()
            if c.is_Number and r.is_Add:
                return _unevaluated_Add(*[c * ri for ri in r.args])
        return e

    return bottom_up(e, do)


from .numbers import Rational
from .power import Pow
from .add import Add, _addsort, _unevaluated_Add
