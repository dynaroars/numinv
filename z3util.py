###########################################
# Miscellaneous / Helpers methods related
# to Z3
#
# Author: ThanhVu (Vu) Nguyen
############################################

from vu_common import vset
from z3 import \
    (is_expr, ctypes, 
     Z3_OP_UNINTERPRETED, Z3_OP_AND, Z3_OP_OR,
     Z3_OP_NOT, Z3_OP_IMPLIES, Z3_OP_IFF, Z3_OP_ITE,  Z3_OP_XOR,
     Z3_REAL_SORT, Z3_INT_SORT, Z3_BOOL_SORT, Z3_DATATYPE_SORT,
     Const, Bool, BoolVal, Int, Real,
     Or, And, Implies, Not,
     is_app, is_app_of, is_const, is_bool, is_not,
     Solver, unsat, sat, unknown, ModelRef)

FALSE = BoolVal(False)
TRUE = BoolVal(True)

def get_z3_version(as_str=False):
    import z3
    print('WARN: deprecated, use z3.get_version() or z3.get_version_string() directly')
    return z3.get_version_string() if as_str else z3.get_version()

def fhash(v):
    """
    Return a 'stronger' hash result than the default hash() method.
    The result from hash() is not enough to distinguish between 2
    z3 expressions in some case.

    Examples:

    >>> from z3 import *
    >>> x1 = Bool('x'); x2 = Bool('x'); x3 = Int('x')
    >>> print x1.hash(),x2.hash(),x3.hash() #BAD: all same hash values
    783810685 783810685 783810685
    >>> print fhash(x1), fhash(x2), fhash(x3)
    (15360046201, 783810685L, 1L) (15360046201, 783810685L, 1L) (15360046201, 783810685L, 2L)
    """

    assert is_expr(v), v
    return (hash(str(v)),v.hash(),v.sort_kind())


def is_expr_var(a):
    """
    Check if a is a variable. E.g. x is a var but x = 3 is not.

    Examples:

    >>> from z3 import *
    >>> assert is_expr_var(Int('7'))
    >>> assert not is_expr_var(IntVal('7'))
    >>> assert is_expr_var(Bool('y'))
    >>> assert not is_expr_var(Int('x') + 7 == Int('y'))

    >>> LOnOff, (On,Off) = EnumSort("LOnOff",['On','Off'])
    >>> Block,Reset,SafetyInjection=Consts("Block Reset SafetyInjection",LOnOff)
    >>> assert not is_expr_var(LOnOff)
    >>> assert not is_expr_var(On)
    >>> assert is_expr_var(Block)
    >>> assert is_expr_var(SafetyInjection)
    """

    return is_const(a) and a.decl().kind() == Z3_OP_UNINTERPRETED

def is_expr_val(a):
    """
    Check if the input formula is a value. E.g. 3 is a value but x = 3 is not.

    Examples:

    >>> from z3 import *
    >>> assert is_expr_val(FALSE)
    >>> assert not is_expr_val(Int('7'))
    >>> assert is_expr_val(IntVal('7'))
    >>> assert not is_expr_val(Bool('y'))
    >>> assert not is_expr_val(Int('x') + 7 == Int('y'))

    >>> LOnOff, (On,Off) = EnumSort("LOnOff",['On','Off'])
    >>> Block,Reset,SafetyInjection=Consts("Block Reset SafetyInjection",LOnOff)
    >>> assert not is_expr_val(LOnOff)
    >>> assert is_expr_val(On)
    >>> assert not is_expr_val(Block)
    >>> assert not is_expr_val(SafetyInjection)
    """
    return is_const(a) and a.decl().kind()!=Z3_OP_UNINTERPRETED

def is_term(a):
    """
    Check if the input formula is a term. In FOL, terms are
    defined as term := const | var | f(t1,...,tn) where ti are terms.

    Examples:

    >>> from z3 import *
    >>> assert is_term(TRUE)
    >>> assert is_term(Bool('x'))
    >>> assert not is_term(And(Bool('x'),Bool('y')))
    >>> assert not is_term(And(Bool('x'),Not(Bool('y'))))
    >>> assert is_term(IntVal(3))
    >>> assert is_term(Int('x'))
    >>> assert is_term(Int('x') + Int('y'))
    >>> assert not is_term(Int('x') + Int('y') > 3)
    >>> assert not is_term(And(Int('x')==0,Int('y')==3))
    >>> assert not is_term(Int('x')==0)
    >>> assert not is_term(3)
    >>> assert not is_term(Bool('x') == (Int('y')==Int('z')))
    """

    if not is_expr(a):
        return False

    if is_const(a):  #covers both const value and var
        return True
    else:  #covers f(t1,..,tn)
        return not is_bool(a) and all(is_term(c) for c in a.children())

CONNECTIVE_OPS = [Z3_OP_NOT,Z3_OP_AND,Z3_OP_OR,Z3_OP_IMPLIES,
                  Z3_OP_IFF,Z3_OP_ITE,Z3_OP_XOR]
def is_atom(a):
    """
    Check if the input formula is an atom. In FOL, atoms are
    defined as atom := t1 = t2 | R(t1,..,tn) where ti are terms.
    In addition, this function also allows Bool variable to
    be terms (in propositional logic, a bool variable is considered term)

    Example:

    >>> from z3 import *
    >>> is_atom(3)
    False

    >>> is_atom(Bool('b'))
    True

    >>> is_atom(Int('x'))
    False

    >>> is_atom(TRUE)
    False

    >>> is_atom(FALSE)
    False

    >>> is_atom(Int('x') + Int('y') > 3)
    True

    >>> is_atom(Bool('x') == TRUE)
    True

    >>> is_atom(Int('x') == 3)
    True

    >>> is_atom(IntVal(3))
    False

    >>> is_atom(Not(TRUE))
    False


    >>> is_atom(Or(TRUE,FALSE))
    False

    >>> is_atom(Or(Bool('b'),Bool('y')))
    False

    """

    if not is_bool(a):
        return False

    if is_expr_val(a):
        return False

    if is_expr_var(a):
        return True

    return is_app(a) and a.decl().kind() not in CONNECTIVE_OPS and\
                all(is_term(c) for c in a.children())


def is_pos_lit(a):
    """
    Check if the input formula is a positive literal,  i.e. an atom

    >>> is_pos_lit(Not(TRUE))
    False
    """
    return is_atom(a)

def is_neg_lit(a):
    """
    Check if the input formula is a negative literal

    EXAMPLES:

    >>> from z3 import *

    >>> is_term(3)
    False

    >>> is_neg_lit(Not(Bool('x')))
    True

    >>> is_neg_lit(Not(FALSE))
    False

    >>> is_neg_lit(TRUE)
    False

    >>> is_neg_lit(FALSE)
    False

    >>> is_neg_lit(Not(Int('x') + Int('y') > 3))
    True

    >>> is_neg_lit(Not(Bool('x') == TRUE))
    True

    >>> is_neg_lit(Not(Int('x') == 3))
    True

    >>> is_neg_lit(Not(TRUE))
    False
    """
    return is_not(a) and is_pos_lit(a.children()[0])

def is_lit(a):
    """
    Check if the input formula is a negative literal

    >>> is_lit(Not(TRUE))
    False
    """
    return is_pos_lit(a) or is_neg_lit(a)

def is_implies(a):
    """
    Check if the input formula has an implication form, e.g. Imply(a ,b)

    Examples:

    >>> from z3 import *
    >>> a,b = Bools('a b')
    >>> is_implies(Or(Not(a), b))
    False
    >>> is_implies(Implies(a, b))
    True
    """
    return is_app_of(a, Z3_OP_IMPLIES)


def _get_vars(f, rs):
    """
    Helper method to obtain variables from a formula f recursively.
    The results are stored in the list rs.
    """
    if is_const(f):
        if is_expr_val(f):
            return rs
        else:  #variable
            return expr_set(rs + [f])

    else:
        for f_ in f.children():
            rs = _get_vars(f_, rs)

        return expr_set(rs)

def get_vars(f):
    """
    Obtain variables from a formula. Make calls to _get_vars()

    Examples:

    >>> from z3 import *
    >>> x,y = Ints('x y')
    >>> a,b = Bools('a b')
    >>> get_vars(Implies(And(x+y==0,x*2==10),Or(a,Implies(a,b==False))))
    [x, y, a, b]
    """
    assert is_expr(f), f

    return _get_vars(f, [])

def _get_literals(f, rs=[]):
    """
    Helper method to obtain literals from a formula f recursively.
    TODO: perhaps this should be in a CNF or DNF format
    because  Not(x and y) returns x, y as literals
    but Not(x) or Not(y) returns Not(x) and Not(y) as literal

    >>> from z3 import *
    >>> x,y = Ints('x y')
    >>> a,b = Bools('a b')

    """
    assert is_expr(f), f

    if is_expr_val(f):
        return rs
    elif is_lit(f):
        return expr_set(rs + [f])
    else:
        for f_ in f.children():
            rs = _get_literals(f_, rs)

        return expr_set(rs)


def get_literals(f):
    """
    Obtain variables from a formula. Make calls to _get_literals().
    """
    assert is_expr(f), f

    return _get_literals(f, [])

def mk_var(name, vsort):
    """
    Create a variable of type vsort.

    Examples:

    >>> from z3 import *
    >>> v = mk_var('real_v', Real('x').sort())
    >>> print v
    real_v

    """
    if vsort.kind() == Z3_INT_SORT:
        v = Int(name)
    elif vsort.kind() == Z3_REAL_SORT:
        v = Real(name)
    elif vsort.kind() == Z3_BOOL_SORT:
        v = Bool(name)
    elif vsort.kind() == Z3_DATATYPE_SORT:
        v = Const(name,vsort)

    else:
        raise AssertionError,\
            'Cannot handle this sort (s: {}, {})'\
            .format(vsort, vsort.kind())

    return v

def mk_literals(v):
    """
    Create literals from a variable v of *finite* domain.
    For example, v = val1, ..., v = val_n,

    >>> from z3 import *

    >>> v = Bool('v')
    >>> mk_literals(v)
    [v, Not(v)]

    >>> T, (ton,toff) = EnumSort("T", ["ton","toff"])
    >>> myT = Const("myT", T)
    >>> mk_literals(myT)
    [myT == ton, myT == toff]


    >>> LeverVal, (loff,lconst,lresume,lrelease) = EnumSort("LeverVal", ["loff","lconst","lresume","lrelease"])
    >>> Lever = Const("Lever", LeverVal)

    >>> mk_literals(Lever)
    [Lever == loff, Not(Lever == loff), Lever == lconst, Not(Lever == lconst), Lever == lresume, Not(Lever == lresume), Lever == lrelease, Not(Lever == lrelease)]

    >>> mk_literals(Int('x'))
    []
    """

    assert is_expr_var(v), v

    if not is_sort_finite(v.sort()):
        return []


    if v.sort().kind() == Z3_BOOL_SORT:
        return [v,Not(v)]
    else:
        vals = get_sort_vals(v.sort())
        if len(vals) == 2:
            return [v== vals[0], v == vals[1]]
        else:
            rs = []
            for val in vals:
                expr = v == val
                rs.append(expr)
                rs.append(Not(expr))

            return rs

def is_sort_finite(vsort):
    """
    Checks if vsort has a finite domain, e.g.
    Bool has finite domain but Int does not

    >>> from z3 import *
    >>> is_sort_finite(Bool('x').sort())
    True
    >>> is_sort_finite(Int('x').sort())
    False

    >>> LeverVal, (loff,lconst,lresume,lrelease) = EnumSort("LeverVal", ["loff","lconst","lresume","lrelease"])
    >>> Lever = Const("Lever", LeverVal)
    >>> is_sort_finite(Lever.sort())
    True
    """
    return vsort.kind() in [Z3_BOOL_SORT, Z3_DATATYPE_SORT]

def get_sort_vals(vsort):
    """
    Return the values of a (finite) sort.
    E.g. a Bool sort has two values: True and False

    >>> from z3 import *
    >>> get_sort_vals(Bool('x').sort())
    [True, False]

    >>> LeverVal, (loff,lconst,lresume,lrelease) = EnumSort("LeverVal", ["loff","lconst","lresume","lrelease"])
    >>> Lever = Const("Lever", LeverVal)

    >>> get_sort_vals(Lever.sort())
    [loff, lconst, lresume, lrelease]
    """
    assert is_sort_finite(vsort),\
        "Cannot obtain values of sort {}".format(vsort)

    if vsort.kind() == Z3_BOOL_SORT:
        return [TRUE, FALSE]
    else:
        return [vsort.constructor(i)()
                for i in range(vsort.num_constructors())]


def vprove(claim, assume=None):
    """
    Shortcut for calling SMT solver to prove the claim

    Examples:

    >>> from z3 import *
    >>> r,m = vprove(TRUE); r,model_str(m,as_str=False)
    (True, None)

    >>> r,m = vprove(Bool('x')); r,model_str(m,as_str=True)
    (False, 'x = False')

    #infinite counter example when proving contradiction
    >>> r,m = vprove(FALSE); r,model_str(m,as_str=False)
    (False, [])

    >>> x,y,z=Bools('x y z')
    >>> r,m = vprove(And(x,Not(x))); r,model_str(m,as_str=True)
    (False, '[]')

    >>> r,m = vprove(TRUE, assume=And(x,Not(x)))
    Traceback (most recent call last):
    ...
    AssertionError: Assumption is always False!

    >>> r,m = vprove(Implies(x,x),assume=y); r,model_str(m,as_str=False)
    (True, None)

    >>> r,m = vprove(And(x,True),assume=y); r,model_str(m,as_str=False)
    (False, [(x, False), (y, True)])

    >>> r,m = vprove(And(x,y),assume=y)
    >>> print r
    False

    >>> print model_str(m,as_str=True)
    x = False
    y = True

    >>> a,b = Ints('a b')
    >>> vprove(a**b == b**a,assume=None)
    (None, None)

    """

    assert is_bool(claim), claim
    assert not assume or is_expr(assume), assume

    to_prove = claim
    if assume:
        assert vprove(Not(assume)) is False, "Assumption is always False!"
        to_prove = Implies(assume,to_prove)

    f = Not(to_prove)

    models = get_models(f,k=1)
    if models is None: #unknown
        return None, None
    elif models is False: #unsat
        return True, None
    else: #sat
        assert isinstance(models,list)

        if models:
            return False, models[0] #the first counterexample
        else:
            return False, []  #infinite counterexample,models


def get_models(f,k):
    """
    Returns the first k models satisfiying f.
    If f is not satisfiable, returns False.
    If f cannot be solved, returns None
    If f is satisfiable, returns the first k models
    Note that if f is a tautology, e.g.\ True, then the result is []

    Based on http://stackoverflow.com/questions/11867611/z3py-checking-all-solutions-for-equation

    EXAMPLES:

    >>> from z3 import *
    >>> x, y = Ints('x y')
    >>> len(get_models(And(0<=x,x <= 4),k=11))
    5
    >>> get_models(And(0<=x**y,x <= 1),k=2) is None
    True
    >>> get_models(And(0<=x,x <= -1),k=2)
    False
    >>> len(get_models(x+y==7,5))
    5
    >>> len(get_models(And(x<=5,x>=1),7))
    5
    >>> get_models(And(x<=0,x>=5),7)
    False

    >>> x = Bool('x')
    >>> get_models(And(x,Not(x)),k=1)
    False
    >>> get_models(Implies(x,x),k=1)
    []
    >>> get_models(TRUE,k=1)
    []

    """

    assert is_expr(f), f
    assert k >= 1, k

    s = Solver()
    s.add(f)

    models = []
    i = 0
    while s.check() == sat and i < k:
        i = i + 1

        m = s.model()

        if not m: #if m == []
            break

        models.append(m)


        #create new constraint to block the current model
        block = Not(And([v() == m[v] for v in m]))
        s.add(block)


    if s.check() == unknown:
        return None
    elif s.check() == unsat and i==0:
        return False
    else:
        return models



def exact_one_model(f):
    """
    return True if f has exactly 1 model, False otherwise.

    EXAMPLES:

    >>> from z3 import *
    >>> x, y = Ints('x y')
    >>> exact_one_model(And(0<=x**y,x <= 0))
    False

    >>> exact_one_model(And(0<=x,x <= 0))
    True

    >>> exact_one_model(And(0<=x,x <= 1))
    False

    >>> exact_one_model(And(0<=x,x <= -1))
    False
    """

    models = get_models(f,k=2)
    if isinstance(models,list):
        return len(models)==1
    else:
        return False



def myBinOp(op,*L):
    """
    Shortcut to apply operation op to a list L.
    Returns None if the list is empty.

    E.g. applying 'And'  over a list of formulas f1,f2..,fn
    yields And(f1,f2,...,fn).

    >>> from z3 import *
    >>> myAnd(*[Bool('x'),Bool('y')])
    And(x, y)

    >>> myAnd(*[Bool('x'),None])
    x

    >>> myAnd(*[Bool('x')])
    x

    >>> myAnd(*[])

    >>> myAnd(Bool('x'),Bool('y'))
    And(x, y)

    >>> myAnd(*[Bool('x'),Bool('y')])
    And(x, y)

    >>> myAnd([Bool('x'),Bool('y')])
    And(x, y)

    >>> myAnd((Bool('x'),Bool('y')))
    And(x, y)

    >>> myAnd(*[Bool('x'),Bool('y'),True])
    Traceback (most recent call last):
    ...
    AssertionError
    """

    assert op == Z3_OP_OR or op == Z3_OP_AND or op == Z3_OP_IMPLIES

    if len(L)==1 and (isinstance(L[0],list) or isinstance(L[0],tuple)):
        L = L[0]

    assert all(not isinstance(l,bool) for l in L)

    L = [l for l in L if is_expr(l)]
    if L:
        if len(L)==1:
            return L[0]
        else:
            if op ==  Z3_OP_OR:
                return Or(L)
            elif op == Z3_OP_AND:
                return And(L)
            else:   #IMPLIES
                return Implies(L[0],L[1])
    else:
        return None


def myAnd(*L): return myBinOp(Z3_OP_AND,*L)
def myOr(*L): return myBinOp(Z3_OP_OR,*L)
def myImplies(a,b):return myBinOp(Z3_OP_IMPLIES,[a,b])


Iff = lambda f,g: And(Implies(f,g),Implies(g,f))



def model_str(m, as_str=True):
    """
    Returned a 'sorted' model by its keys.
    e.g. if the model is y = 3 , x = 10, then the result is
    x = 10, y = 3

    EXAMPLES:
    see doctest examples from function prove()

    """
    assert m is None or m == [] or isinstance(m,ModelRef)

    if m :
        vs = [(v,m[v]) for v in m]
        vs = sorted(vs,key=lambda (a,_): str(a))
        if as_str:
            return '\n'.join(['{} = {}'.format(k,v) for (k,v) in vs])
        else:
            return vs
    else:
        return str(m) if as_str else m


def check_sat(a, solver=None):
    """
    Check the satisfiabily of a formula.

    Examples

    >>> from z3 import *
    >>> check_sat(FALSE)
    unsat

    >>> p, q = Bools('p q')
    >>> f = Not(And(p, q)) == Or(Not(p), Not(q)) #tautology
    >>> check_sat(Not(f))
    unsat

    >>> check_sat(And(p, q),solver=Solver())
    sat

    >>> x, y = Ints('x y')
    >>> f = x*x*x == y*y
    >>> check_sat(f)
    sat
    """

    assert is_expr(a), a

    if solver:
        solver.add(a)
        result = solver.check()
        solver.reset()
    else:
        solver = Solver()        
        solver.add(a)
        result = solver.check()

    return result
    
def is_sat(a, solver=None):
    """ Check if a formula is satisiable """
    return check_sat(a,solver) == sat

def is_tautology(a, solver=None):
    """
    Check if claim is a tautology (always True)

    EXAMPLES:

    >>> from z3 import *
    >>> x,y = Bools('x y')
    >>> is_tautology(Implies(x,x))
    True

    >>> is_tautology(Implies(x,y))
    False

    >>> is_tautology(x==(x==TRUE))
    True

    >>> is_tautology(Not(x)==(x==FALSE))
    True

    >>> assert is_tautology(TRUE)
    >>> assert not is_tautology(FALSE)

    >>> pre_x = Bool('pre_x')
    >>> f = And(Not(pre_x == FALSE), x == FALSE)
    >>> g = And(Not(pre_x == TRUE), x == TRUE)
    >>> assert not is_tautology(Or(f,g),Solver())

    """
    return check_sat(Not(a), solver) == unsat

def is_contradiction(claim, solver=None):
    """
    Check if claim is a contradiction (always False)
    EXAMPLES:
    >>> from z3 import *
    >>> x,y=Bools('x y')
    >>> assert is_contradiction(FALSE)
    >>> assert not is_contradiction(TRUE)
    >>> assert not is_contradiction(x)
    >>> assert not is_contradiction(Implies(x,y))
    >>> assert not is_contradiction(Implies(x,x),Solver())
    >>> assert is_contradiction(And(x,Not(x)))
    """
    return check_sat(claim,solver) == unsat

def is_equiv(f, g, solver=None):
    """
    # Check if two formulas are equivalent

    >>> assert not is_equiv(Int('x'),Int('y'))
    >>> assert is_equiv(Int('x'),Int('x'),Solver())
    >>> assert is_equiv(And(Bool('x'),Not(Bool('x'))), Or(FALSE,FALSE))
    """
    print "VERY SLOW, just do is_tautology(f == g) instead"
    if fhash(f) == fhash(g):
        return True
    else:
        return is_tautology(f == g, solver)

def is_imply(f, g, solver=None):
    """
    >>> from z3 import *
    >>> x, y = Ints('x y')
    >>> assert is_imply(x >= 3, x >= -5)
    """
    assert is_expr(f)
    assert is_expr(g)
    
    if fhash(f) == fhash(g):
        return True
    else:
        return is_tautology(Implies(f,g), solver)
    

def expr_member(f, gs):
    """
    Check if a formula f is in the list gs using hashing.

    >>> from z3 import *
    >>> x = Int('x')
    >>> y = Real('y')
    >>> z = Bool('z')

    #this shows Python 'in' doesn't work on formulas
    >>> x in [y]
    True

    #but expr_member works
    >>> expr_member(x,[y])
    False

    >>> expr_member(x,[x])
    True
    >>> expr_member(x,[])
    False
    >>> expr_member(x,[y, z])
    False
    >>> expr_member(x,[y,])
    False
    >>> expr_member(x,[y, x])
    True
    >>> expr_member(z,[z])
    True

    #This hash-based expr_member doesn't work on complicate formulas
    >>> expr_member(z, [Not(Not(z))])
    False
    """
    assert is_expr(f), f
    assert all(is_expr(g) for g in gs), gs

    return any(fhash(f) == fhash(g) for g in gs)


def expr_member_smt(f, gs):
    """
    Check if a formula f is in the list gs using SMT.

    >>> z = Bool('z')
    >>> expr_member_smt(z, [Not(Not(z))])
    True
    """
    assert is_expr(f), f
    assert all(is_expr(g) for g in gs), gs

    return any(is_equiv(f, g) for g in gs)


def expr_set(fs):
    """
    Return a set of formulas (i.e. all items are distinct) using hashing
    """
    assert all(f is None or is_expr(f) for f in fs), fs
    
    return vset(fs,  lambda f: None if f is None else fhash(f))

def expr_set_smt(fs):
    """
    Return a set of formulas (i.e. all items are distinct) using SMT
    """
    eset = []
    for f in fs:
        if not expr_member_smt(f, eset):
            eset.append(f)
    return eset


def expr_subset(S1,S2):
    """
    """
    return all(expr_member(expr,S2) for expr in S1)


def expr_set_intersection_smt(S1, S2):

    S2_ = expr_set_smt(S2)
    return [s for s in S1 if expr_member(s, S2_)]

def expr_multiset_intersection_smt(Ss):
    assert len(Ss) >= 2, 'need at least 2 input sets'

    iset = Ss[0]
    for S in Ss[2:]:
        iset = expr_set_intersection_smt(iset, S)

    return iset

def expr_subset_smt(S1,S2):
    """
    """
    return all(expr_member_smt(expr,S2) for expr in S1)


def is_even(x):
    return x%2 == 0

def is_odd(x):
    return Not(is_even(x))

if __name__ == '__main__':
    import doctest
    doctest.testmod()

