import abc
from collections import OrderedDict, MutableSet, MutableMapping
import collections
import itertools
import os.path
import sage.all

import vu_common as CM
from sageutil import is_sage_expr
import settings
logger = CM.VLog('alg')
logger.level = settings.logger_level  

import miscs
from cpa import RT   #Reachability Tool
import solver

class Src(object):
    def __init__(self, filename):
        assert os.path.isfile(filename), filename
        self.filename = filename

    def parse(self): return self._parse(self.filename)
    
    def instrDisproves(self, invs, invdecls, lineno):
        return self.instr(self.filename, ".dp.c",
                          invs, invdecls, lineno, self.mkDisproves)
    
    def instrAssertsRT(self, dinvs, inps, inps_d, startFun="mainQ"):
        assert isinstance(dinvs, DInvs), dinvs
        assert (inps_d is None or
                (isinstance(inps_d, OrderedDict) and inps_d)), inps_d
        
        assert isinstance(inps, Inps), inps

        if inps_d:
            parts = self.mkPrintfArgs(inps_d)
        else:
            parts = (None, None)
            
        _mk = lambda invs, loc: RT.mkAssertInvs(invs, loc, parts)
        stmts = self.mkProgStmts(self.filename, dinvs, _mk)

        #comment startFun(..argv[]) and add symbolic input
        stmts_ = []
        for stmt in stmts:
            if startFun in stmt and "argv" in stmt:
                for varname, (vartyp, (minV, maxV)) in inps_d.iteritems():
                    stmt = RT.mkSymbolic(varname, vartyp)
                    stmts_.append(stmt)
                    if minV is not None and maxV is not None:
                        stmts__ = RT.mkAssumeRanges(varname, minV, maxV)
                        stmts_.extend(stmts__)

                #klee_assume(x!=0 || y!=1); klee_assume(x!=2 || y!=3);
                if inps:
                    stmts__ = RT.mkAssumeInps(inps)
                    stmts_.extend(stmts__)
                
                #call mainQ(inp0, ..);
                stmt = "{}({});".format(
                    startFun, ",".join(map(str, inps_d.iterkeys())))
                stmts_.append(stmt)
                
            if (all(x in stmt for x in ['assert', '(', ')', ';']) and
                '//' not in stmt):
                
                stmt = RT.mkAssert(stmt);
                stmts_.append(stmt)
            else:
                stmts_.append(stmt)

        stmts = stmts_
            
        #add header, e.g., #include ...
        stmts = RT.mkHeaders() + stmts
        
        fname = self.filename + ".assert.c"
        CM.vwrite(fname, '\n'.join(stmts))
        CM.vcmd("astyle -Y {}".format(fname))
        return fname

    @classmethod
    def _parse(cls, filename, startFun="mainQ", traceIndicator="//%%%traces:"):
        """
        Return 
        inpdecls = {'x':'int', 'y':'double', ..}
        invdecls = {'lineno' : {'x':'int'; 'y':'double'}}
        """
        def mkVarsDict(s):
            #%%%indicator double x , double y .. ->  {x: int, y: double}
            #where x and y are SAGE's symbolic variables
            contents = (x.split() for x in s.split(','))
            try:
                return OrderedDict(
                    (sage.all.var(k.strip()), t.strip()) for t,k in contents )
            except ValueError:
                return None

        inpdecls, invdecls, lineno = OrderedDict(), OrderedDict(), None
        for i,l in enumerate(CM.iread(filename)):            
            i = i + 1
            l = l.strip()
            if not l: continue

            if startFun in l and l.endswith(' {'):  #void startFun(int x, double y) {
                l = l.split('(')[1].split(')')[0]  #int x, double y
                inpdecls = mkVarsDict(l)

            elif l.startswith(traceIndicator):
                invdecls = mkVarsDict(miscs.stripTo(l, ':'))
                lineno = i
                
        assert invdecls
        assert (inpdecls is None or
                (isinstance(inpdecls, OrderedDict) and inpdecls)), inpdecls
        assert lineno
        return inpdecls, invdecls, lineno


    @classmethod
    def mkPrintfArgs(cls, vars_d):
        """
        Return 2 strings representing 2 args to a printf stmt
        sage: vars_d = OrderedDict([('x','int'),('y','double')])
        sage: Src.mkPrintfArgs(vars_d)
        ('%d %g', 'x, y')
        """
        assert isinstance(vars_d, OrderedDict) and vars_d, vars_d
        p1 = []
        for k in vars_d:
            typ = vars_d[k]
            if isinstance(vars_d[k], tuple): #(typ, (minV, maxV))
                typ = vars_d[k][0]
                
            if typ == "int":
                a = "%d"
            else:
                a = "%g"
            p1.append(a)
        p1 = ' '.join(p1)
        p2 = ', '.join(map(str, vars_d.iterkeys()))
        return p1, p2

    @classmethod
    def mkDisproves(cls, invs, vars_d, lineno):
        """
        sage: vars_d = OrderedDict([('x','int'),('y','double')])
        sage: Src.mkPrintfVarStr(vars_d, 12)
        '12: %d %g\\n", x, y'
        """
        assert lineno > 0, lineno
        p1, p2 = cls.mkPrintfArgs(vars_d)
        vstr = '@ line {}: {}\\n", {}'.format(lineno, p1, p2)
        stmts = []
        for inv in invs:
            dStmt = "if(!({})) printf(\"disproved {} {});".format(
                inv, inv, vstr)
            stmts.append(dStmt)
        return stmts

    @classmethod
    def mkProgStmts(cls, filename, invs, invdecls, lineno, mk_f):
        assert lineno > 0;
        
        stmts = []
        for i, l in enumerate(CM.iread(filename)):
            i = i + 1
            l = l.strip()
            if not l: continue
            stmts.append(l)
            
            if i == lineno:
                assert invdecls
                stmts_ = mk_f(invs, invdecls, lineno)
                stmts.extend(stmts_)
                
        return stmts
    
    @classmethod
    def instr(cls, filename, filePostfix, invs, invdecls, lineno, mkStmts):
        stmts = cls.mkProgStmts(filename, invs, invdecls, lineno, mkStmts)
        
        fname = filename + filePostfix
        CM.vwrite(fname, '\n'.join(stmts))
        CM.vcmd("astyle -Y {}".format(fname))
        return fname

# inv     
is_inv = lambda inv: inv is 0 or inv.is_relational()
def strOfInv(inv):
    if is_sage_expr(inv):
        inv = miscs.elim_denom(inv)
        s = miscs.strOfExp(inv)
    else:
        s = str(inv)
    return s

class Trace(CM.HDict):
    """
    Hashable traces
    """

    def __str__(self):
        return " ".join("{}={}".format(x,y) for x,y in self.iteritems())

    @property
    def _dict(self):
        """
        Some Sage substitution requires dict format
        """
        try:
            return self._d
        except AttributeError:
            self._d = dict(self)
            return self._d
        
    @classmethod
    def parse(cls, tracefile, invdecls):
        """
        parse trace for new traces
        """
        assert isinstance(tracefile, str), tracefile        
        assert isinstance(invdecls, dict) and invdecls, invdecls

        dtraces = {}
        for l in CM.iread_strip(tracefile):
            #disproved x + y == 0 @ line 20: 924 9 0 1 9 924
            inv_s, trace_s = l.split(':')
            #lineno = parts[0].strip()  #l22
            #assert lineno in invdecls, (lineno, invdecls)

            #inv
            inv_s, line_s = inv_s.strip().split('@')
            inv = inv_s.replace('disproved', '').strip()

            #traces
            tracevals = trace_s.strip().split()
            tracevals = map(miscs.ratOfStr, tracevals)
            if not miscs.checkVals(tracevals):
                logger.detail('skipping trace: {}'.format(tracevals))
                continue
            
            ss = invdecls.keys()
            assert len(ss) == len(tracevals)
            trace = cls(zip(ss, tracevals))

            if inv not in dtraces:
                dtraces[inv] = set()
            dtraces[inv].add(trace)
            
        return dtraces
    
class DIG2(object):
    def __init__(self, filename, tmpdir):
        assert os.path.isfile(filename), filename
        assert os.path.isdir(tmpdir), tmpdir
        self.filename = filename
        self.tmpdir = tmpdir

    def start(self, seed, deg):
        assert isinstance(seed, (int,float)), seed
        assert deg >= 1 or callable(deg), deg

        self.initialize(seed, deg)

        exprs = set()
        traces = [] #total traces
        inps = set()
        #stats = {inv -> traces or proved or unknown}
        stats = self.check([0], inps, nNeededTraces=None)
        for inv in stats:
            if isinstance(stats[inv], set):
                traces.extend(stats[inv])

        curIter = 0
        while True:
            if not traces:
                logger.debug("no more traces")
                break

            invs, nNeededTraces = self.infer(traces, exprs)
            
            curIter += 1
            logger.info(
                "iter {}, invs {}, inps {}, traces {}, rand {}".
                format(curIter, len(invs), len(inps), len(traces),
                       sage.all.randint(0,100)))
            
            if nNeededTraces:
                stats_ = self.check([0], inps, nNeededTraces)
                traces = []
                for inv in stats_:
                    if isinstance(stats_[inv], set):
                        traces.extend(stats_[inv])
                continue

            if not invs:
                logger.warn("found no invs")
                break
            
            stats = self.check(invs, inps, nNeededTraces=None)
            traces = []
            for inv in stats:
                if isinstance(stats[inv], list):
                    traces.extend(stats[inv])

        invs = [inv for inv in stats if isinstance(stats[inv], bool)]
        logger.info('\n'.join(map(str,invs)))
        return invs


    def check(self, invs, einps, nNeededTraces):
        assert invs, invs
        assert isinstance(einps, set)
        assert nNeededTraces is None or nNeededTraces > 0, nNeededTraces

        invs = [strOfInv(inv) for inv in invs]
        src = self.src.instrDisproves(invs, self.invdecls, self.lineno)
        exe = "{}.exe".format(src)
        #-lm for math.h to work
        cmd = "gcc -lm {} -o {}".format(src, exe) 
        rs, rs_err = CM.vcmd(cmd)
        assert not rs, rs
        assert not rs_err, rs_err
        
        inps = miscs.genInitInps(len(self.inpdecls), solver.maxV)

        if os.path.isfile(self.tcsFile): os.remove(self.tcsFile)
        for inp in inps:
            einps.add(inp)
            
            inp = ' '.join(map(str, inp))
            cmd = "{} {} >> {}".format(exe, inp, self.tcsFile)
            logger.detail(cmd)
            CM.vcmd(cmd)
        dtraces = Trace.parse(self.tcsFile, self.invdecls)
        stats = {}
        for inv in invs:
            stats[inv] = dtraces[inv] if inv in dtraces else False
        return stats
        
    def infer(self, traces, exprs):
        assert traces        
        ss = self.ss
        deg = self.deg
        logger.debug("infer with vs: {}, deg: {}, traces: {}, exprs: {}".format(
            len(ss), deg, len(traces), len(exprs)))

        terms = miscs.getTerms(ss, deg)  #cache
        solvercls = solver.EqtSolver
        invs, nMoreTraces = solvercls().solve(terms, traces, exprs)
        invs = solvercls.refine(invs)
        return invs, nMoreTraces

        
    def initialize(self, seed, deg):
        import random        
        random.seed(seed)
        sage.all.set_random_seed(seed)
        logger.info('set seed to: {} (test {})'
                    .format(seed, sage.all.randint(0,100)))

        fname = os.path.basename(self.filename)
        src = os.path.join(self.tmpdir, fname)
        _, rs_err = CM.vcmd("astyle -Y < {} > {}".format(self.filename, src))
        assert not rs_err, rs_err
        logger.debug("src: {}".format(src))
        
        self.src = Src(src)
        self.inpdecls, self.invdecls, self.lineno = self.src.parse()
        self.ss = [sage.all.var(k) for k in self.invdecls]

        if callable(deg):
            self.deg = deg(len(self.ss))
            logger.info("autodeg {}".format(self.deg))
        else:
            self.deg = deg
            
        #tracefile
        self.tcsFile =  "{}.tcs".format(self.src.filename)
