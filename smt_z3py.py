from sage.all import (operator, var, sage_eval)
import z3

from vu_common import is_empty, is_list
from z3util import vprove
from sageutil import is_sage_expr, is_sage_int, is_sage_real, get_vars

"""
Adding z3py Api to SAGE_PATH
E.g.
in ~/.bash_profile
export Z3=$DEVEL/z3
export SAGE_PATH=$DROPBOX/code/git/invgen:$Z3/python
"""

#todo
# def toZ3d(p, typD, cache):
#     "typD = {'x': 'int', 'y': 'double'}"
#     "cache = {x:sageexpr => x:z3expr}"
#     assert is_sage_expr(p), p
#     assert isinstance(typD, dict), typD
#     def retval(p):
#         if p.is_symbol():
#             _f = z3.Real if is_real else z3.Int
#         else:
#             _f = z3.RealVal if is_real else z3.IntVal

#         return _f(str(p))

#     try:
#         oprs = p.operands()
#     except Exception:
#         return retval(p)

#     if is_empty(oprs):
#         return retval(p)
#     else:
#         op = p.operator()

#         #z3 has problem w/ t^c , so use t*t*t..
#         if op == operator.pow:
#             assert len(oprs) == 2, oprs
#             t, c = oprs
#             t = toZ3(t, is_real)
#             vs = [t] * c
#             z3exp = reduce(operator.mul, vs)
#         else:
#             oprs = [toZ3(o, is_real) for o in oprs]
#             z3exp = reduce(op, oprs)

#         assert z3.is_expr(z3exp), z3exp
#         return z3exp


def toZ3(p, is_real):
    """
    Convert a Sage expression to a Z3 expression

    Initially implements with a dictionary containing variables
    e.g. {x:Real('x')} but the code is longer and more complicated.
    This implemention does not require a dictionary pass in.

    Todo: cache this function

    sage: toZ3(x*x*x, False)
    x*x*x
    """
    assert is_sage_expr(p), p

    def retval(p):
        if p.is_symbol():
            _f = z3.Real if is_real else z3.Int
        else:
            _f = z3.RealVal if is_real else z3.IntVal

        return _f(str(p))

    try:
        oprs = p.operands()
    except Exception:
        return retval(p)

    if is_empty(oprs):
        return retval(p)
    else:
        op = p.operator()

        #z3 has problem w/ t^c , so use t*t*t..
        if op == operator.pow:
            assert len(oprs) == 2, oprs
            t, c = oprs
            t = toZ3(t, is_real)
            vs = [t] * c
            z3exp = reduce(operator.mul, vs)
        else:
            oprs = [toZ3(o, is_real) for o in oprs]
            z3exp = reduce(op, oprs)

        assert z3.is_expr(z3exp), z3exp
        return z3exp


def imply(fs, gs):
    """
    Checks if the set f of formulas implies the set f of formulas

    sage: var('x y')
    (x, y)

    sage: assert imply([x-6==0],x*x-36==0)
    sage: assert imply([x-6==0,x+6==0],x*x-36==0)
    sage: assert not imply([x*x-36==0],x-6==0)
    sage: assert not imply([x-6==0],x-36==0)
    sage: assert imply(x-7>=0,x>=6)
    sage: assert not imply(x-7>=0,x>=8)
    sage: assert not imply(x-6>=0,x-7>=0)
    sage: assert not imply([x-7>=0,y+5>=0],x+y-3>=0)
    sage: assert imply([x-7>=0,y+5>=0],x+y-2>=0)
    sage: assert imply([x-2*y>=0,y-1>=0],x-2>=0)
    sage: assert not imply([],x-2>=0)
    sage: assert imply([x-7>=0,y+5>=0],x+y-2>=0)
    sage: assert imply([x^2-9>=0,x>=0],x-3>=0)
    sage: assert not imply([1/2*x**2 - 3/28*x + 1 >= 0],1/20*x**2 - 9/20*x + 1 >= 0)
    sage: assert imply([1/20*x**2 - 9/20*x + 1 >= 0],1/2*x**2 - 3/28*x + 1 >= 0)
    sage: assert imply([x-6==0],x*x-36==0)
    sage: assert not imply([x+7>=0,y+5>=0],x*y+36>=0)
    sage: assert not imply([x+7>=0,y+5>=0],x*y+35>=0)
    sage: assert not imply([x+7>=0,y+5>=0],x*y-35>=0)
    sage: assert not imply([x+7>=0],x-8>=0)
    sage: assert imply([x+7>=0],x+8>=0)
    sage: assert imply([x+7>=0],x+8.9>=0)
    sage: assert imply([x>=7,y>=5],x*y>=35)
    sage: assert not imply([x>=-7,y>=-5],x*y>=35)
    sage: assert imply([x-7>=0,y+5>=0],[x+y-2>=0,x>=2-y])

    """
    if is_empty(fs) or is_empty(gs):
        return False #conservative approach

    if not isinstance(fs, list): fs = [fs]
    if not isinstance(gs, list): gs = [gs]

    fs = [toZ3(f, is_real=True) for f in fs]
    gs = [toZ3(g, is_real=True) for g in gs]

    claim = z3.Implies(z3.And(fs), z3.And(gs))

    is_proved, _ = vprove(claim)
    return is_proved



def getConstraints(m, resultAsDict=False):
    """
    Input a model m, returns its set of constraints in either
    1) sage dict {x:7,y:10}
    1) z3 expr [x==7,y==0]


    sage: S = z3.Solver()
    sage: S.add(z3.Int('x') + z3.Int('y') == z3.IntVal('7'))
    sage: S.check()
    sat
    sage: M = S.model()
    sage: d = getConstraints(M, resultAsDict=True)
    sage: sorted(d.items(), key=lambda(k,_): str(k))
    [(x, 7), (y, 0)]
    sage: getConstraints(M)
    [y == 0, x == 7]
    sage: S.reset()

    """

    assert m is not None, m

    if resultAsDict:  #sage format
        rs = [(var(str(v())),sage_eval(str(m[v]))) for v in m]
        rs = dict(rs)

        assert all(is_sage_expr(x) for x in rs.keys())
        assert all(is_sage_real(x) or is_sage_int(x) for x in rs.values())

    else:  #z3 format
        rs = [v()==m[v] for v in m]
        assert all(z3.is_expr(x) for x in rs)

    return rs

#useful shortcuts
def exp_int(x):
    """
    sage: exp_int(x>10)
    x > 10
    """
    return x if z3.is_expr(x) else toZ3(x, is_real=False)

def exp_real(x):
    return x if z3.is_expr(x) else toZ3(x, is_real=True)

def map_exp_int(*xs):
    """
    sage: map_exp_int(x>10,x>20)
    [x > 10, x > 20]
    """
    return map(lambda x: exp_int(x), xs)

def map_exp_real(*xs):
    """
    """
    return map(lambda x: exp_real(x), xs)


def and_int(*xs):
    return z3.And(map_exp_int(*xs))

def and_real(*xs):
    return z3.And(map_exp_real(*xs))

def or_int(*xs):
    return z3.Or(map_exp_int(*xs))

def or_real(*xs):
    return z3.Or(map_exp_real(*xs))


def implies_int(c1,c2):
    return z3.Implies(exp_int(c1), exp_int(c2))

def implies_real(c1,c2):
    return z3.Implies(exp_real(c1),exp_real(c2))

class SMT_Z3(object):
    """
    SMT Helpers. Uses Z3py
    """

    @staticmethod
    def to_z3(p):
        print("WARN: deprecated, don't use eval()")
        typ = "{} = z3.Ints('{}')"
        vs = map(str, get_vars(p))
        z3_vars_decl = typ.format(','.join(vs),' '.join(vs))
        exec(z3_vars_decl)
        f = eval(str(p))
        print z3.is_expr(f)

    @staticmethod
    def to_z3exp(p, is_real):
        print("WARN: deprecated, don't use to_z3exp()")
        return toZ3(p, is_real)

    @staticmethod
    def imply(fs, gs):
        print("WARN: deprecated, don't use imply()")
        return imply(fs, gs)


    @staticmethod
    def get_constraints(m, result_as_dict=False):
        print("WARN: deprecated, don't use get_constraints()")
        return getConstraints(m, result_as_dict)
        
    #useful shortcuts
    @staticmethod
    def exp_int(x):
        print("WARN: deprecated, don't use")
        return exp_int(x)

    @staticmethod
    def exp_real(x):
        print("WARN: deprecated, don't use")
        return exp_real(x)

    @staticmethod
    def map_exp_int(*xs):
        print("WARN: deprecated, don't use")
        return map_exp_int(*xs)

    @staticmethod
    def map_exp_real(*xs):
        print("WARN: deprecated, don't use")
        return map_exp_real(*xs)

    @staticmethod
    def and_int(*xs):
        print("WARN: deprecated, don't use")
        return and_int(*xs)

    @staticmethod
    def and_real(*xs):
        print("WARN: deprecated, don't use")
        return and_real(*xs)

    @staticmethod
    def or_int(*xs):
        print("WARN: deprecated, don't use")
        return or_int(*xs)

    @staticmethod
    def or_real(*xs):
        print("WARN: deprecated, don't use")
        return or_real(*xs)


    @staticmethod
    def implies_int(c1,c2):
        print("WARN: deprecated, don't use")
        return implies_int(c1,c2)


    @staticmethod
    def implies_real(c1,c2):
        print("WARN: deprecated, don't use")
        return implies_real(c1, c2)



"""
S = z3.Solver()
S.add(z3.Int('x') + z3.Int('y') == z3.IntVal('7'))
S.check()
sat
M = S.model()
M.eval(M.decls()[0])
crash

"""





