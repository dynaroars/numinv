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
    
    def instrAssertsRT(self, invs, inps, inps_d, invdecls, lineno, startFun="mainQ"):
        assert isinstance(invs, set) and invs, dinvs
        assert isinstance(inps, set), inps
        assert (inps_d is None or
                (isinstance(inps_d, OrderedDict) and inps_d)), inps_d

        
        #mk_f(invs, invdecls, lineno)            
        _mk = lambda myinvs, _, loc: RT.mkAssertInvs(myinvs, loc)
        stmts = self.mkProgStmts(self.filename, invs, invdecls, lineno, _mk)

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
                
            elif (all(x in stmt for x in ['assert', '(', ')', ';']) and
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
                
            a = "%d" if typ == "int" else "%g"
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
            dStmt = "if(!((int){})) printf(\"disproved {} {});".format(
                inv, inv, vstr)
            stmts.append(dStmt)
        return stmts

    @classmethod
    def mkProgStmts(cls, filename, invs, invdecls, lineno, mk_f):
        assert invs, invs
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

def printInvs(stats):
    invs = [inv for inv in stats if isinstance(stats[inv], bool)]
    if invs:
        logger.warn("found {} invs\n{}".format(
            len(invs), '\n'.join(map(strOfInv, invs))))

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
            print inv_s, trace_s
            #lineno = parts[0].strip()  #l22
            #assert lineno in invdecls, (lineno, invdecls)

            #inv
            inv_s, line_s = inv_s.strip().split('@')
            print inv_s, line_s
            inv = inv_s.replace('disproved', '').strip()
            print inv
            
            #traces
            tracevals = trace_s.strip().split()
            tracevals = map(miscs.ratOfStr, tracevals)
            if not miscs.checkVals(tracevals):
                #logger.detail('skipping trace: {}'.format(tracevals))
                continue
            
            ss = invdecls.keys()
            assert len(ss) == len(tracevals)
            trace = cls(zip(ss, tracevals))

            print inv
            print dtraces
            CM.pause()
            if inv not in dtraces:
                dtraces[inv] = set()
            dtraces[inv].add(trace)
            
        return dtraces


class MySet(MutableSet):
    __metaclass__ = abc.ABCMeta
    def __init__(self): self.__set__ = set()
    def __len__(self): return len(self.__set__)
    def __iter__(self): return iter(self.__set__)    
    def __str__(self): return ", ".join(map(str, sorted(self)))
    def discard(self): raise NotImplementedError("discard")
    
    @abc.abstractmethod
    def __contains__(self, inp): return inp in self.__set__
    @abc.abstractmethod
    def add(self, inp):
        notIn = False
        if inp not in self.__set__:
            notIn = True
            self.__set__.add(inp)
        return notIn
    
class Inv(object):
    PROVED = "p"
    DISPROVED = "d"
    UNKNOWN = "u"
    
    def __init__(self, inv):
        assert inv == 0 or inv == 1 or inv.is_relational(), inv
        self.inv = inv
        
        self.resetStat()
        self.resetTemplateID()
        
    def __str__(self, printStat=False):
        
        if is_sage_expr(self.inv):
            inv = miscs.elim_denom(self.inv)
            s = miscs.strOfExp(inv)
        else:
            s = str(self.inv)

        if printStat: s = "{} {}".format(s, self.stat)
        return s
    
    def __hash__(self): return hash(self.inv)
    def __repr__(self): return repr(self.inv)
    def __eq__(self, o): return self.inv.__eq__(o.inv)
    def __ne__(self, o): return not self.inv.__eq__(o.inv)

    def getStat(self): return self._stat    
    def setStat(self, stat):
        assert stat in {self.PROVED, self.DISPROVED, self.UNKNOWN}, stat
        self._stat = stat
    stat = property(getStat, setStat)

    def resetStat(self): self._stat = None
        
    @property
    def isProved(self): return self.stat == self.PROVED
    @property
    def isDisproved(self): return self.stat == self.DISPROVED
    @property
    def isUnknown(self): return self.stat == self.UNKNOWN

    @classmethod
    def mkFalse(cls): return cls(0)

    def getTemplateID(self): return self._tid
    def setTemplateID(self, tid):
        self._tid = tid
    templateID = property(getTemplateID, setTemplateID)
    def resetTemplateID(self): self._tid = None

class Invs(MySet):
    def __contains__(self, inv):
        assert isinstance(inv, Inv), inv
        return super(Invs, self).__contains__(inv)

    def add(self, inv):
        assert isinstance(inv, Inv), inv
        return super(Invs, self).add(inv)

    def remove(self, inv):
        assert isinstance(inv, Inv), inv
        self.__set__.remove(inv)

    def clear(self):
        self.__set__.clear()

    def __str__(self, printStat=False):
        return ", ".join(map(lambda inv: inv.__str__(printStat), sorted(self)))

    def resetStats(self):
        for inv in self:
            inv.resetStat()

    def removeDisproved(self):
        newInvs = Invs()
        for inv in self:
            if not inv.isDisproved:
                newInvs.add(inv)

        return newInvs
    
class DIG2(object):
    def __init__(self, filename, tmpdir):
        assert os.path.isfile(filename), filename
        assert os.path.isdir(tmpdir), tmpdir
        self.filename = filename
        self.tmpdir = tmpdir

    def approx(self, invs, inps, traces, solvercls):
        exprs = set()
        curIter = 0
        
        while True:
            curIter += 1
            logger.info(
                "iter {}, invs {}, inps {}, traces {}, exprs {}, rand {}".
                format(curIter, len(invs), len(inps), len(traces), len(exprs),
                       sage.all.randint(0,100)))
            logger.debug(str(invs))

            if not traces:
                logger.debug("no more traces")
                break

            try:
                invs_ = self.infer(traces, exprs, solvercls)
                logger.debug(str(invs_))
            except solver.NotEnoughTraces as e:
                logger.detail(str(e))
                invs__ = Invs()
                invs__.add(Inv(0))
                traces = self.check(invs__, inps, solvercls.minV, solvercls.maxV)
                continue
            except solver.SameInsts as e:
                logger.detail(str(e))
                break  

            if not invs_ or invs_ == invs:
                break

            invs = invs_
            traces = self.check(invs, inps, solvercls.minV, solvercls.maxV)
            invs = invs.removeDisproved()
            
        return invs

    def start(self, seed, deg):
        assert isinstance(seed, (int,float)), seed
        assert deg >= 1 or callable(deg), deg

        self.initialize(seed, deg)

        inps = set()
        invs = Invs()        
        invs.add(Inv(0))
        
        #solvercls = solver.EqtSolver
        solvercls = solver.RangeSolverWeak

        traces = self.check(invs, inps, solvercls.minV, solvercls.maxV)
        invs = invs.removeDisproved()
        invs = self.approx(invs, inps, traces, solvercls)


        logger.info("final checking {} candidate invs\n{}"
                    .format(len(invs), invs))
        _ = self.check(invs, inps, solvercls.minV*10, solvercls.maxV*10,
                       quickcheck=False)
        invs.removeDisproved()
                                                                            
        logger.debug(str(invs))
        return invs

    def mexec(self, exe, inps):
        assert isinstance(exe, str) and exe.endswith(".exe"), exe
        assert isinstance(inps, set) and inps, inps
        
        if os.path.isfile(self.tcsFile): os.remove(self.tcsFile)
        for inp in inps:
            inp = ' '.join(map(str, inp))
            cmd = "{} {} >> {}".format(exe, inp, self.tcsFile)
            logger.detail(cmd)
            CM.vcmd(cmd)
        dtraces = Trace.parse(self.tcsFile, self.invdecls)
        print "babab", dtraces
        return dtraces

    def checkRT(self, invs, einps, exe, minV, maxV):
        if self.inpdecls:
            inps_d = OrderedDict(
                (vname, (vtyp, (minV, maxV)))
                for vname, vtyp in self.inpdecls.iteritems())
        else:
            inps_d = None

        for inv in invs:
            einps_ =  set(CM.HDict(zip(self.inpdecls, inp)) for inp in einps)
            rtSrc = self.src.instrAssertsRT(
                set([inv]), einps_, inps_d,
                self.invdecls, self.lineno)
            _, inps = RT(rtSrc, self.tmpdir).getDInps()  #run
            if inps:
                logger.info("RT disproved {}".format(inv))
                inps_ = set()
                for inp in inps:
                    inp = tuple([inp[str(k)] for k in self.inpdecls])
                    einps.add(inp)
                    inps_.add(inp)
                print 'ba', inps_
                dtraces = self.mexec(exe, inps_)
                return dtraces

        return {}
                
    def check(self, invs, einps, minV, maxV, quickcheck=True):
        assert isinstance(invs, Invs) and invs, invs 
        assert isinstance(einps, set) #existing inps
        assert isinstance(quickcheck, bool), quickcheck
        
        src = self.src.instrDisproves(invs, self.invdecls, self.lineno)
        exe = "{}.exe".format(src)
        cmd = "gcc -lm {} -o {}".format(src, exe) 
        rs, rs_err = CM.vcmd(cmd)
        assert not rs, rs
        assert not rs_err, rs_err
        print exe

        dtraces = None
        if quickcheck:
            inps = miscs.genInps(len(self.inpdecls), maxV)
            for inp in inps: einps.add(inp)
            dtraces = self.mexec(exe, inps)
            
        
        if not dtraces:
            logger.debug("invoke rt")
            dtraces = self.checkRT(invs, einps, exe, minV, maxV)

        print 'hi', dtraces
        traces = []
        for inv in invs:
            k = str(inv)
            if k in dtraces:
                logger.detail("{} disproved".format(inv))
                inv.stat = Inv.DISPROVED
                traces.extend(dtraces[k])
            else:
                inv.stat = Inv.UNKNOWN

        return traces
        
    def infer(self, traces, exprs, solvercls):
        assert traces
        
        logger.debug("infer: vs {}, deg {}, traces {}, exprs {}".format(
            len(self.ss), self.deg, len(traces), len(exprs)))

        terms = miscs.getTerms(self.ss, self.deg)  #cache
        invs = solvercls().solve(terms, traces, exprs)
        newInvs = Invs()
        for inv in invs:
            newInvs.add(Inv(inv))
        return newInvs

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
