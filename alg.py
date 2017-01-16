import abc
from collections import OrderedDict
import collections
import itertools
import os.path
import sage.all

import vu_common as CM
from sageutil import is_sage_expr

import miscs
from src import Src
from klee import KLEE 
from solver import EqtSolver, RangeSolver, OctSolver, IeqSolver

import settings
logger = CM.VLog('alg')
logger.level = settings.logger_level  

#Inputs
class Inp(tuple):
    pass

class Inps(set):
    def __init__(self): super(Inps, self).__init__(set())

    def __contains__(self, inp):
        assert isinstance(inp, Inp), inp
        return super(Inps, self).__contains__(inp)

    def add(self, inp):
        assert isinstance(inp, Inp), inp
        return super(Inps, self).add(inp)
        
#Traces
class Trace(tuple):
    maxV = 10000
    
    def valOk(self):
        minV = -1 * self.maxV
        return all(minV <= v <= self.maxV for v in self)
    
    @classmethod
    def parse(cls, tracefile, invdecls):
        """
        parse trace for new traces
        """
        assert isinstance(tracefile, str), tracefile        
        assert isinstance(invdecls, dict) and invdecls, invdecls

        traces = DTraces()
        for l in CM.iread_strip(tracefile):
            #l22: 8460 16 0 1 16 8460
            parts = l.split(':')
            assert len(parts) == 2
            lineno = parts[0].strip()  #l22
            assert lineno in invdecls, (lineno, invdecls)

            tracevals = parts[1].strip().split()
            tracevals = cls(map(miscs.ratOfStr, tracevals))
            traces.add(lineno, tracevals)
        return traces

class Traces(set):
    def __contains__(self, trace):
        assert isinstance(trace, Trace), trace
        return super(Traces, self).__contains__(trace)

    def add(self, trace):
        assert isinstance(trace, Trace), trace
        return super(Traces, self).add(trace)

    def __str__(self, printStat=False):
        return ", ".join(map(str, sorted(self)))


class DTraces(dict):
    def add(self, loc, trace):
        assert isinstance(loc, str), loc
        assert isinstance(trace, Trace), trace

        if not trace.valOk():
            return False

        if loc not in self:
            self[loc] = Traces()

        notIn = False
        if trace not in self[loc]:
            self[loc].add(trace)
            notIn = True
        return notIn

    def update(self, traces):
        """
        Update dtraces to contain conents of self and return diffs
        """
        newTraces = DTraces()
        for loc in self:
            for trace in self[loc]:
                notIn = traces.add(loc, trace)
                if notIn:
                    _ = newTraces.add(loc, trace)
                else:
                    logger.detail("{} exist or too large".format(trace))
        return newTraces

    @property
    def siz(self): return sum(map(len, self.itervalues()))

    def __str__(self):
        return "\n".join("{}: {}".format(loc, len(traces))
                         for loc, traces in self.iteritems())    
    
    
class Inv(object):
    PROVED = "p"
    DISPROVED = "d"
    UNKNOWN = "u"
    
    def __init__(self, inv):
        assert inv == 0 or inv == 1 or inv.is_relational(), inv
        self.inv = inv
        self.resetStat()
        
    def __str__(self, printStat=False):
        
        if is_sage_expr(self.inv):
            s = miscs.strOfExp(self.inv)
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

class Invs(set):
    def __contains__(self, inv):
        assert isinstance(inv, Inv), inv
        return super(Invs, self).__contains__(inv)

    def add(self, inv):
        assert isinstance(inv, Inv), inv
        notIn = False
        if inv not in self:
            notIn = True
            super(Invs, self).add(inv)
        return notIn

    def __str__(self, printStat=False):
        return ", ".join(map(lambda inv: inv.__str__(printStat), sorted(self)))

class DInvs(dict):
    @property
    def siz(self): return sum(map(len, self.itervalues()))

    def __str__(self, printStat=False):
        return "\n".join("{}: {}".format(loc, invs.__str__(printStat))
                         for loc, invs in self.iteritems())

    def add(self, loc, inv):
        assert isinstance(loc, str), loc
        assert isinstance(inv, Inv), inv

        if loc not in self:
            self[loc] = Invs()
        return self[loc].add(inv)
    

    def __setitem__(self, loc, invs):
        assert isinstance(loc, str), loc
        assert isinstance(invs, Invs), invs
        
        super(DInvs, self).__setitem__(loc, invs)

    def resetStats(self):
        for loc in self:
            for inv in self[loc]:
                inv.resetStat()
        
    def merge(self, invs):
        assert isinstance(invs, DInvs), invs
        mergedInvs = DInvs()
        
        for loc in invs:
            for inv in invs[loc]:
                if not inv.isDisproved: 
                    self.add(loc, inv)

    def removeDisproved(self):
        dinvs = DInvs()
        for loc in self:
            for inv in self[loc]:
                assert inv.stat is not None, inv
                if not inv.isDisproved:
                    dinvs.add(loc, inv)

        return dinvs
    
    def update(self, dinvs):
        assert isinstance(dinvs, DInvs), dinvs
        deltas = DInvs()
        for loc in self:
            if loc not in dinvs:
                dinvs[loc] = self[loc]
                deltas[loc] = self[loc]
            elif dinvs[loc] != self[loc]:
                new_invs = Invs()
                for inv in self[loc]:
                    if inv not in dinvs[loc]:
                        new_invs.add(inv)
                    else:
                        invs_l = list(dinvs[loc])
                        old_inv = invs_l[invs_l.index(inv)]
                        if inv.stat != old_inv.stat:
                            inv.stat = old_inv.stat
                dinvs[loc] = self[loc]
                deltas[loc] = new_invs

        return deltas

    @classmethod
    def mkFalses(cls, locs):
        dinvs = DInvs()
        for loc in locs:
            dinvs.add(loc, Inv.mkFalse())
        return dinvs
        

class DIG2(object):
    def __init__(self, filename):
        assert os.path.isfile(filename), filename
        
        import tempfile
        self.tmpdir = tempfile.mkdtemp(dir=settings.tmpdir, prefix="DIG2_")
        self.filename = filename
        basename = os.path.basename(self.filename)
        src = os.path.join(self.tmpdir, basename)
        _, rs_err = CM.vcmd("astyle -Y < {} > {}".format(self.filename, src))
        assert not rs_err, rs_err
        logger.debug("src: {}".format(src))
        self.src = Src(src)
        self.inpdecls, self.invdecls = self.src.parse()
        
        self.printfSrc = self.src.instrPrintfs(self.invdecls)
        self.exeFile = "{}.exe".format(self.printfSrc)
        #-lm for math.h to work
        cmd = "gcc -lm {} -o {}".format(self.printfSrc, self.exeFile) 
        CM.vcmd(cmd)
        #tracefile
        self.tcsFile =  "{}.tcs".format(self.printfSrc)
        
    def start(self, seed, maxdeg, maxterm, doEqts, doIeqs, ieqTyp):
        assert isinstance(seed, (int,float)), seed
        assert isinstance(doEqts, bool), doEqts
        assert isinstance(doIeqs, bool), doIeqs

        import random
        random.seed(seed)
        sage.all.set_random_seed(seed)
        logger.info('set seed to: {} (test {})'
                    .format(seed, sage.all.randint(0,100)))

        ##determine degree
        maxvars = max(self.invdecls.itervalues(), key=lambda d: len(d))
        if maxdeg and maxterm:
            deg = maxdeg
        elif maxdeg:
            deg = maxdeg
        else:
            if maxterm:
                deg = miscs.getDeg(len(maxvars), maxterm)
            else:
                deg = miscs.getDeg(len(maxvars), 200)
            logger.info("autodeg {}".format(deg))
        

        logger.info("check reachability")
        dinvs, traces, inps = self.checkReach()
        if not traces:
            return dinvs

        _f = lambda mlocs: "{} locs: {}".format(
            len(mlocs), ', '.join(map(str, mlocs)))
            
        if doEqts:
            logger.info("infer eqts at {}".format(_f(traces.keys())))
            eqts = self.approx(deg, traces, inps)
            dinvs.merge(eqts)

        if doIeqs:
            # if ieqTyp.startswith("oct"):
            #         solverCls = OctSolver
            #     else:
            #         solverCls = RangeSolver
            logger.info("infer ieqs at {}".format(_f(traces.keys())))
            binvs = self.genOcts(einps, etraces)
            for inv in binvs: invs.add(inv)
            
            dinvs_ = None
            dinvs.merge(dinvs_)
                
        logger.info("final check {} invs".format(dinvs.siz))
        logger.detail(dinvs.__str__(printStat=True))
        
        #final tests
        dinvs.resetStats()
        _ = self.getInpsNoRange(dinvs, inps)
        dinvs = dinvs.removeDisproved()

        logger.info("got {} invs\n{} (test {})"
                    .format(dinvs.siz, dinvs.__str__(printStat=True),
                            sage.all.randint(0,100)))
                    
        return dinvs

    def getInps(self, dinvs, inps, minV, maxV, doSafe):
        """
        return new inps (and also add them to inps)
        """
        assert isinstance(dinvs, DInvs), dinvs
        assert isinstance(inps, Inps), inps        
        assert isinstance(doSafe, bool), doSafe

        def addInps(klInps, newInps, inps):
            for inp in klInps:
                if self.inpdecls:
                    assert inp and len(self.inpdecls) == len(inp)
                    inp = Inp(inp)
                else:
                    inp = Inp()
                assert inp not in inps, inp                
                inps.add(inp)
                newInps.add(inp)

        if self.inpdecls:
            inps_d = OrderedDict((vname, (vtyp, (minV, maxV)))
                                 for vname, vtyp in self.inpdecls.iteritems())
        else:
            inps_d = None
        
        newInps = Inps()
        if doSafe:
            #prove individually
            for loc,invs in dinvs.iteritems():
                for inv in invs:
                    if inv.stat is not None: continue

                    dinvs_ = DInvs()
                    dinvs_.add(loc, inv)
                    klSrc = self.src.instrAsserts(dinvs_, inps, inps_d)
                    klDInps, isSucc = KLEE(klSrc, self.tmpdir).getDInps()
                    try:
                        klInps = klDInps[loc][str(inv)]
                        addInps(klInps, newInps, inps)
                        inv.stat = Inv.DISPROVED
                    except KeyError:
                        inv.stat = Inv.PROVED if isSucc else Inv.UNKNOWN

            for loc,invs in dinvs.iteritems():
                assert(inv.stat is not None for inv in invs)

        else:
            #do all at once
            dinvs_ = DInvs()
            for loc, invs in dinvs.iteritems():
                for inv in invs:
                    if inv.stat is None:
                        dinvs_.add(loc, inv)

            klSrc = self.src.instrAsserts(dinvs_, inps, inps_d)
            klDInps, _ = KLEE(klSrc, self.tmpdir).getDInps()
            
            #IMPORTANT: getDInps() returns an isSucc flag (false if timeout),
            #but it's not useful here (when haveing multiple klee_asserts)
            #because even if isSucc, it doesn't guarantee to generate cex
            #for a failed assertions (that means we can't claim if an assertion
            #without cex is proved).
            for loc, invs in dinvs.iteritems():
                for inv in invs:
                    if inv.stat is not None: continue
                    try:
                        klInps = klDInps[loc][str(inv)]
                        addInps(klInps, newInps, inps)
                        inv.stat = Inv.DISPROVED
                    except KeyError:
                        pass

        return newInps
                    
    def getInpsRange(self, dinvs, inps, doSafe):
        minv, maxv = IeqSolver.minV, IeqSolver.maxV, 
        return self.getInps(dinvs, inps, minv, maxv, doSafe)

    def getInpsNoRange(self, dinvs, inps):
        minv, maxv = IeqSolver.minV*10, IeqSolver.maxV*10, 
        return self.getInps(dinvs, inps, minv, maxv, doSafe=True)
                            
    def getTraces(self, inps):
        """
        Run program on inps and get traces
        """
        assert isinstance(inps, Inps) and inps, inps
        
        if os.path.isfile(self.tcsFile): os.remove(self.tcsFile)
        
        for inp in inps:
            inp_ = ' '.join(map(str, inp))
            cmd = "{} {} >> {}".format(self.exeFile, inp_, self.tcsFile)
            logger.detail(cmd)
            CM.vcmd(cmd)

        traces = Trace.parse(self.tcsFile, self.invdecls)
        return traces

    def checkReach(self):
        #check for reachability using inv False (0)
        dinvs = DInvs.mkFalses(self.invdecls)        
        inps = Inps()

        #use some initial inps first
        rinps = miscs.genInitInps(len(self.inpdecls), IeqSolver.maxV)
        for inp in rinps: inps.add(Inp(inp))
        traces = self.getTraces(inps)
        unreachLocs = [loc for loc in dinvs if loc not in traces]
        if unreachLocs:
            logger.debug("use RT to generate traces for {}".format(
                ','.join(map(str, unreachLocs))))
            unreachInvs = DInvs.mkFalses(unreachLocs)
            unreachTraces = self.checkInvs(unreachInvs, inps, doSafe=True)
            unreachTraces.update(traces)

            

        #remove FALSE invs indicating unreached locs
        for loc in traces:
            assert traces[loc]
            dinvs[loc].clear()

        return dinvs, traces, inps
        
    def checkInvs(self, dinvs, inps, doSafe):
        assert isinstance(dinvs, DInvs), dinvs
        assert isinstance(inps, Inps), inps        

        logger.detail("checking {} invs:\n{}".format(
            dinvs.siz, dinvs.__str__(printStat=True)))
        newInps = self.getInpsRange(dinvs, inps, doSafe)
        
        if not newInps:
            return DTraces()
        else:
            newDTraces = self.getTraces(newInps)
            logger.debug("got {} traces from {} inps"
                         .format(newDTraces.siz, len(newInps)))
            return newDTraces

    def approx(self, deg, traces, inps):
        """iterative refinment algorithm"""
        
        assert deg >= 1, deg
        assert isinstance(traces, DTraces) and traces, traces                
        assert isinstance(inps, Inps), inps

        dinvs = DInvs()
        locs = traces.keys()
        vss = dict((loc, [sage.all.var(k) for k in self.invdecls[loc]])
                   for loc in locs)
        terms = dict((loc, miscs.getTerms(vss[loc], deg)) for loc in vss)
        
        curIter = 0
        while True:
            if not locs:
                logger.debug("no new traces")
                break

            dinvs_, locsMoreTraces = self.inferEqts(deg, locs, terms, traces)
            deltas = dinvs_.update(dinvs)
            
            curIter += 1
            logger.info(
                "iter {}, invs {}, inps {}, traces {}, rand {}".
                format(curIter, dinvs.siz, len(inps), traces.siz,
                       sage.all.randint(0,100)))

            if locsMoreTraces:
                logger.debug("getting more traces for {} locs: {}"
                             .format(len(locsMoreTraces),
                                     ",".join(map(str, locsMoreTraces))))
                dinvsFalse = DInvs.mkFalses(locsMoreTraces)
                traces_ = self.checkInvs(dinvsFalse, inps, doSafe=False)
                newTraces = traces_.update(traces)
                locs = newTraces.keys()
                continue

            #deltas means some changed
            #(this could be adding to or removing from dinvs, thus
            #deltas.siz could be 0, e.g., dinvs has a, b and dinvs_ has a)
            if deltas:
                logger.debug("{} new invs".format(deltas.siz))
                if deltas.siz:
                    logger.debug(deltas.__str__(printStat=True))
            else:
                logger.debug("no new invs")
                break

            traces_ = self.checkInvs(dinvs, inps, doSafe=False)
            newTraces = traces_.update(traces)
            locs = newTraces.keys()
            
        return dinvs


    #Eqts
    def inferEqts(self, deg, locs, terms, traces):
        """
        call DIG's algorithm to infer eqts from traces
        """
        assert isinstance(locs, list) and locs, locs
        assert isinstance(traces, DTraces) and traces, traces        

        locsMoreTraces = []
        dinvs = DInvs()
        for loc in locs:
            assert traces[loc], loc
            terms_ = terms[loc]
            logger.debug("loc {}, terms {}, deg {}, traces {}".format(
                loc, len(terms_), deg, len(traces[loc])))
            try:
                #cache ?
                traces_ = (dict(zip(self.invdecls[loc], tracevals))
                           for tracevals in traces[loc])
                solver = EqtSolver(traces_)
                invs = solver.solve(terms_)
                invs = EqtSolver.refine(invs)
                for inv in invs:
                    dinvs.add(loc, Inv(inv))
                    
            except miscs.NotEnoughTraces as ex:
                logger.info("loc {}: {}".format(loc, ex))         
                locsMoreTraces.append(loc)

        return dinvs, locsMoreTraces


    #Ieqs
    def guessCheck(self, term, etraces, minV, maxV, oMinV, oMaxV):
        assert minV <= maxV, (minV, maxV)
        assert oMinV < oMaxV, (oMinV, oMaxV)
        assert isinstance(etraces, set), etraces
        
        if minV == maxV:
            return maxV
        elif maxV - minV == 1:
            inv = Inv(term <= minV)
            print 'final rt {}'.format(inv)
            disproved = self.checkRT(Invs.mk(inv), set(),
                                     oMinV, oMaxV, quickbreak=True)
            return maxV if disproved else minV
            
        v = sage.all.ceil((maxV + minV)/2.0)
        inv = Inv(term <= v)
        #print 'rt {}'.format(inv)
        traces = self.check(Invs.mk(inv), set(), oMinV, oMaxV, dorandom=False)
        print term, minV, maxV, 'checking ', inv
        if traces: #disproved
            minV = max(term.subs(tc._dict) for tc in traces)
            for tc in traces: etraces.add(tc)
            print 'disproved', minV
        else:
            maxV = v
            print 'proved', maxV

        return self.guessCheck(term, etraces, minV, maxV, oMinV, oMaxV)


    def genOcts(self, einps, etraces):
        logger.debug("generate octagonal invs")

        mminV, mmaxV = self.minV + 1, self.maxV - 1
        #octagonal invs        
        solvercls = solver.OctSolver()
        octTerms = solvercls.getTerms(self.ss)  #x,-x, x-y, -x+y, ..
        # print octTerms
        # CM.pause()
        
        octInvs = [Inv(ot <= mmaxV) for ot in octTerms]
            
        octD = dict(zip(octInvs, octTerms))

        octInvs = Invs.mk(octInvs)
        for oInv in octInvs:
            print oInv
        CM.pause()
        disproved = self.checkRT(octInvs, einps,
                                 self.unboundMinV, self.unboundMaxV,
                                 quickbreak=False)

        print disproved
        CM.pause("disproved")
        octInvs.removeDisproved(disproved)
        invs = Invs()
        for octInv in octInvs:
            octTerm = octD[octInv]            
            logger.detail("refine {} (compute upperbound for '{}')"
                          .format(octInv, octTerm))

            mminV = max(octTerm.subs(tc._dict) for tc in etraces)
            boundV = self.guessCheck(octTerm, etraces,
                                     mminV, mmaxV,
                                     self.unboundMinV, self.unboundMaxV)
            inv = Inv(octTerm <= boundV)
            print 'obtained', inv
            invs.add(inv)
            logger.detail("{}".format(inv))            

        if invs:
            logger.info("{} ieqs (rtCalls {})\n{}"
                        .format(len(invs), self.rtCalls, invs))
            
        return invs
    
