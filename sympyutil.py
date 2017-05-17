from sympy import Expr, Symbol, Integer, oo

is_sympy_expr = lambda x:  isinstance(x, Expr)
is_sympy_symbol = lambda x: isinstance(x, Symbol) #use this instead of x.is_Symbol
is_sympy_int = lambda x: isinstance(x, Integer)
is_sympy_inf = lambda x: x == oo or x == -oo
is_sympy_int_inf = lambda x: is_sympy_int(x) or is_sympy_inf(x)

def is_sympy_rel(x, rel=None):
    """
    >>> from sympy.abc import x,y
    >>> assert not is_sympy_rel(7.2)
    >>> assert not is_sympy_rel(x)
    >>> assert not is_sympy_rel(x+7)
    >>> assert is_sympy_rel(Eq(x,3), Equality)

    >>> assert is_sympy_rel(x<=3, LessThan)
    >>> assert not is_sympy_rel(x<=3, StrictLessThan)
    >>> assert not is_sympy_rel(x+3, StrictLessThan)

    >>> assert is_sympy_rel(x+y<=3)
    """
    try:
        if not x.is_Relational:
            return False

        if rel is None:
            return True
        else:
            return isinstance(x, rel)
    except AttributeError: #e.g. when call on an integer
        return False

def get_vars(ps):
    """
    Returns a list of uniq variables from a list of properties

    EXAMPLES:

    >>> a,b,c,x=symbols('a,b,c,x')
    >>> assert [a, b, c, x] == get_vars([x**3 + a**2+b+2, c**2-b-100, b**2 + c**2 + a**3>= 1])
    >>> assert [a, b, c] == get_vars(a**2+b+5*c+2)
    >>> assert [x] == get_vars(x+x**2)
    >>> assert [] == get_vars([3])
    >>> assert [] == get_vars(3)
    >>> assert [b, x] == get_vars([3,'x + c',x+b])


    """

    ps = ps if isinstance(ps,list) else [ps]

    vs = []
    for p in ps:
        try:
            vs = vs + list(p.free_symbols)
        except Exception:
            continue


    if __debug__:
        assert all(v.is_Symbol for v in vs)

    return sorted(set(vs))


def mk_rhs_0(p):
    """
    p: is_sympy_rel

    >>> from sympy.abc import x,y
    >>> assert mk_rhs_0(x - y  >= 3) == (x - y - 3 >= 0)
    >>> assert mk_rhs_0(x - y  - 3 >= 0) == (x - y - 3 >= 0)
    >>> assert mk_rhs_0(0 <= x - y - 3) == (x - y - 3 >= 0)
    >>> assert mk_rhs_0(Eq(0,x)) == Eq(-x, 0)
    >>> assert mk_rhs_0(Eq(10,-x)) == Eq(x + 10, 0)
    >>> assert mk_rhs_0(LessThan(x,oo)) == LessThan(x - oo, 0)
    >>> assert mk_rhs_0(LessThan(x,-oo)) == LessThan(x + oo, 0)
    >>> assert mk_rhs_0(GreaterThan(x, oo)) == GreaterThan(x - oo, 0)
    >>> assert mk_rhs_0(GreaterThan(oo, x)) == GreaterThan(-x + oo, 0)


    >>> mk_rhs_0(x - y - 3)
    Traceback (most recent call last):
    ...
    AttributeError: 'Add' object has no attribute 'rhs'

    """
    try:
        if not p.rhs == 0:
            lhs = p.lhs - p.rhs
            rhs = 0
            p = p.__class__(lhs, rhs)

        return p

    except AttributeError:
        raise


def get_coefs_terms(p):
    """
    >>> from sympy.abc import x,y,a,b,c

    >>> assert get_coefs_terms(x - y - 3) == {S(1): -3, x: 1, y: -1}
    >>> assert get_coefs_terms(x - y >= 3) == {S(1): -3, x: 1, y: -1}
    >>> assert get_coefs_terms(Eq(a**2+b+5*c+2,0)) == {S(1): 2, b: 1, c: 5, a**2: 1}
    >>> assert get_coefs_terms(10*a**2+3*b+5*c+2) == {S(1): 2, b: 3, c: 5, a**2: 10}
    >>> assert get_coefs_terms(LessThan(a - b, oo)) == {S(1): -oo, a: 1, b: -1}
    >>> assert get_coefs_terms(S(7)) == {S(1): 7}
    >>> assert get_coefs_terms(oo) == {oo:1}
    >>> assert get_coefs_terms(-oo)== {-oo:1}

    >>> get_coefs_terms(10/3.0*a**2+3*b+5*c+2)
    {1: 2, c: 5, a**2: 3.33333333333333, b: 3}



    """
    if is_sympy_rel(p):
        f = mk_rhs_0(p).lhs
    else:
        f = p

    #convert defaultdict to a normal dict
    return dict(f.as_coefficients_dict())

def to_z3(p):
    """
    Convert a sympy expression to Z3 expression

    >>> from sympy.abc import x,y,z
    >>> to_z3(x * 7.3 >= y)
    73/10*x >= y
    >>> to_z3(7.3 >= z)
    z <= 73/10

    """
    if __debug__:
        assert isinstance(p, Expr) and p.is_Relational, p

    import z3


    ss = map(str,get_vars(p))
    if len(ss) >= 2:
        typ = "{} = z3.Reals('{}')"
        z3_vars_decl = typ.format(','.join(ss),' '.join(ss))
    else:
        typ = "{} = z3.Real('{}')"
        z3_vars_decl = typ.format(ss[0],ss[0])

    exec(z3_vars_decl)
    f = eval(str(p))
    if __debug__:
        assert z3.is_expr(f), f
    return f



if __name__ == "__main__":
    from sympy import Eq, StrictLessThan, LessThan, GreaterThan, Equality, symbols, S
    import doctest
    doctest.testmod()

