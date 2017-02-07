#Todo: eqts, after generate candidates first time, check them against init traces
#then add the cex traces to exprs

from collections import OrderedDict
import os.path
import sage.all

import vu_common as CM

from miscs import Miscs, NotEnoughTraces
from src import Src
import solver

import settings
logger = CM.VLog('alg')
logger.level = settings.logger_level  

from ds import Inp, Inps, Trace, Traces, DTraces, Inv, Invs, DInvs
from prover import Prover

class Gen(object):
    def __init__(self, invdecls, prover):
        self.invdecls = invdecls
        self.prover = prover

class GenEqts(Gen):
    def __init__(self, invdecls, prover):
        super(GenEqts, self).__init__(invdecls, prover)

    def getInitTraces(self, loc, deg, traces, inps):
        vs = tuple(self.invdecls[loc])
        terms = Miscs.getTerms([sage.all.var(k) for k in vs], deg)
        template, uks = solver.Template.mk(terms, 0, retCoefVars=True)
        nEqtsNeeded = int(1.5 * len(uks))
        traces_ = [tc.mydict(vs) for tc in traces[loc]]
        exprs = template.instantiateTraces(traces_, nEqtsNeeded)

        while nEqtsNeeded > len(exprs):
            logger.debug("{}: need more traces ({} eqts, need >= {})"
                         .format(loc, len(exprs), nEqtsNeeded))
            dinvsFalse = DInvs.mkFalses([loc])
            newTraces, dcexs = self.prover.checkRange(dinvsFalse, traces, inps,
                                                      doSafe=False, doExec=True)
            if loc not in newTraces:
                logger.warn("{}: enough traces".format(loc))
                return
                
            traces_ = [tc.mydict(vs) for tc in newTraces[loc]]
            newExprs = template.instantiateTraces(traces_, nEqtsNeeded - len(exprs))
            for expr in newExprs:
                assert expr not in exprs
                exprs.add(expr)
                    
        return template, uks, exprs

    @classmethod
    def refine(cls, sols):
        if not sols: return sols
        sols = solver.reducePoly(sols)
        sols = [solver.elimDenom(s) for s in sols]
        #don't allow large coefs
        sols = [s for s in sols if all(abs(c) <= 100 for c in solver.getCoefs(s))]
        return sols        

    @classmethod
    def solve(cls, eqts, uks, template):
        logger.debug("solving {} unknowns using {} eqts".format(len(uks), len(eqts)))
        rs = sage.all.solve(eqts, uks, solution_dict=True)
        eqts = template.instantiateSols(rs)
        eqts = cls.refine(eqts)
        return eqts
        
    def infer(self, loc, template, uks, exprs, traces, inps):
        assert isinstance(exprs, set) and exprs, exprs

        vs = tuple(self.invdecls[loc])
        cache = set()
        eqts = set() #results
        exprs = list(exprs)
        
        newTraces = True
        while newTraces:
            newTraces = False
            logger.debug("{}: infer using {} exprs".format(loc, len(exprs)))
            newEqts = self.solve(exprs, uks, template)
            unchecks = [eqt for eqt in newEqts if eqt not in cache]

            if not unchecks:
                logger.info("no new results -- break")
                continue
                
            for p in unchecks: cache.add(p)
            logger.debug('{}: {} candidates:\n{}'.format(
                loc, len(newEqts), '\n'.join(map(str, newEqts))))

            logger.debug("{}: check {} unchecked ({} candidates)"
                         .format(loc, len(unchecks), len(newEqts)))

            dinvs = DInvs.mk(loc, Invs.mk(map(Inv, unchecks)))
            newTraces, dcexs = self.prover.checkRange(
                dinvs, traces, inps, doSafe=False, doExec=True)

            _ = [eqts.add(inv) for loc in dinvs for inv in dinvs[loc]
                 if not inv.isDisproved]
            
            if loc not in newTraces:  #no counterexamples
                logger.info("cannot disprove anything -- break")
                continue
            
            newTraces = True
            #for each disproved inv, just use 1 cex
            cexs = [map(Miscs.ratOfStr, dcexs[loc][inv].pop()) for inv in dcexs[loc]]
            cexs = [Trace(tc).mydict(vs) for tc in cexs]
            exprs_ = template.instantiateTraces(cexs, None)
            logger.debug("{}: new cex exprs {}".format(loc, len(exprs_)))
            exprs.extend(exprs_)

                     
        logger.debug("got {} eqts".format(len(eqts)))
        if eqts: logger.debug('\n'.join(map(str, eqts)))
        return eqts
                
    def gen(self, deg, traces, inps):
        assert deg >= 1, deg
        assert isinstance(traces, DTraces) and traces, traces                
        assert isinstance(inps, Inps), inps

        dexprs = dict()
        #first obtain enough traces
        for loc in traces.keys():
            exprs = self.getInitTraces(loc, deg, traces, inps)
            if exprs:
                dexprs[loc] = exprs
            
        #then solve/prove in parallel
        dinvs = DInvs()
        for loc in dexprs:
            template, uks, exprs = dexprs[loc]
            eqts = self.infer(loc, template, uks, exprs, traces, inps)
            dinvs[loc] = Invs.mk(eqts)
        return dinvs

        

class GenIeqs(Gen):
    def __init__(self, invdecls, prover):
        super(GenIeqs, self).__init__(invdecls, prover)

    def gen(self, deg, traces, inps):
        assert deg >= 1, deg
        assert isinstance(traces, DTraces), traces
        assert isinstance(inps, Inps), inps

        assert isinstance(traces, DTraces) and traces, traces                
        assert isinstance(inps, Inps), inps

        mymaxv  = 10
        
        maxV = mymaxv
        minV = -1*maxV
        
        ubmaxV = maxV+10
        ubminV = -1*ubmaxV

        locs = traces.keys()
        vss = [[sage.all.var(k) for k in self.invdecls[loc]]  for loc in locs]
        termss = [solver.getTermsFixedCoefs(vs, 2) for vs in vss]
        logger.info("{} locs: check upperbounds for {} terms".format(
            len(locs), sum(map(len, termss))))
        
        refs = {loc: {Inv(t <= maxV): t for t in terms}
                for loc, terms in zip(locs, termss)}
        ieqs = DInvs((loc, Invs.mk(refs[loc].keys())) for loc in refs)
        _ = self.prover.check(ieqs, traces, inps, ubminV, ubmaxV, doSafe=True)
        ieqs = ieqs.removeDisproved()

        tasks = [(loc, refs[loc][ieq]) for loc in ieqs for ieq in ieqs[loc]]

        logger.info("{} locs: compute upperbounds for {} terms".format(
            len(locs), len(tasks)))
        
        def _f(loc, term):
            mminV = self.getMinV(term, loc, traces, minV, maxV)
            
            logger.debug("{}: compute ub for '{}', start w/ min {}, maxV {})"
                         .format(loc, term, mminV, maxV))
            
            disproves = set()
            boundV = self.guessCheck(loc, term, traces, inps, 
                                     mminV, maxV, ubminV, ubmaxV, disproves)
            if boundV not in disproves and boundV not in {maxV, minV}:
                inv = Inv(term <= boundV)
                logger.debug("got {}".format(inv))
                return inv
            else:
                return None


        def wprocess(tasks, Q):
            rs = [(loc, _f(loc, term)) for loc, term in tasks]
            if Q is None:
                return rs
            else:
                Q.put(rs)

        do_parallel = len(tasks) >= 2                
        if do_parallel:
            from vu_common import get_workloads
            from multiprocessing import (Process, Queue, 
                                         current_process, cpu_count)
            Q=Queue()
            workloads = get_workloads(tasks, 
                                      max_nprocesses=cpu_count(),
                                      chunksiz=2)

            logger.debug("workloads 'guesscheck' {}: {}"
                         .format(len(workloads),map(len,workloads)))

            workers = [Process(target=wprocess,args=(wl,Q))
                       for wl in workloads]

            for w in workers: w.start()
            wrs = []
            for _ in workers: wrs.extend(Q.get())
        else:
            wrs = wprocess(tasks, Q=None)
                    

        rs = [(loc, inv) for loc, inv in wrs if inv]
        dinvs = DInvs()
        for loc, inv in rs:
            if loc not in dinvs: dinvs[loc] = Invs()
            dinvs[loc].add(inv)
        return dinvs

    def getMinV(self, octTerm, loc, traces, minV, maxV):
        ltraces = [dict(zip(self.invdecls[loc], tracevals))
                   for tracevals in traces[loc]]
        ts = [octTerm.subs(tc) for tc in ltraces]
        try:
            mminV = max(minV, max(t for t in ts if t < maxV))
        except ValueError:
            mminV = minV
        return mminV

    def guessCheck(self, loc, term, traces, inps, minV, maxV,
                   ubMinV, ubMaxV, disproves):
        assert minV <= maxV, (minV, maxV, term)
        assert ubMinV < ubMaxV, (ubMinV, ubMaxV)
        assert isinstance(traces, DTraces), traces
        assert isinstance(disproves, set), disproveds

        if minV == maxV: return maxV
        elif maxV - minV == 1:
            if minV in disproves:
                return maxV
            inv = Inv(term <= minV)
            inv_ = DInvs.mk(loc, Invs.mk([inv]))
            dTraces = self.prover.check(inv_, traces, inps, ubMinV, ubMaxV,
                                     doSafe=True, doExec=True)
            if loc in dTraces:
                assert dTraces[loc]
                disproves.add(minV)
                return maxV
            else:
                return minV

        v = sage.all.ceil((maxV + minV)/2.0)
        inv = Inv(term <= v)
        inv_ = DInvs.mk(loc, Invs.mk([inv]))
        dTraces = self.prover.check(inv_, traces, inps, ubMinV, ubMaxV,
                                 doSafe=True)

        if loc in dTraces: #disproved
            assert dTraces[loc]
            disproves.add(v)
            traces_ = (dict(zip(self.invdecls[loc], tracevals))
                       for tracevals in dTraces[loc])
            minV = max(term.subs(tc) for tc in traces_)
        else:
            maxV = v

        return self.guessCheck(loc, term, traces, inps,
                               minV, maxV, ubMinV, ubMaxV,
                               disproves)

class DIG2(object):
    def __init__(self, filename):
        assert os.path.isfile(filename), filename

        import tempfile
        tmpdir = tempfile.mkdtemp(dir=settings.tmpdir, prefix="DIG2_")
        basename = os.path.basename(filename)
        src = os.path.join(tmpdir, basename)
        _, rs_err = CM.vcmd("astyle -Y < {} > {}".format(filename, src))
        assert not rs_err, rs_err
        logger.debug("src: {}".format(src))
        src = Src(src)
        self.inpdecls, self.invdecls = src.parse()
        printfSrc = src.instrPrintfs(self.invdecls)
        exeFile = "{}.exe".format(printfSrc)
        cmd = "gcc -lm {} -o {}".format(printfSrc, exeFile) #-lm for math.h
        CM.vcmd(cmd)
        tcsFile =  "{}.tcs".format(printfSrc) #tracefile

        self.prover = Prover(src, self.inpdecls, self.invdecls,
                             exeFile, tcsFile, tmpdir)
        logger.info("analyze {}".format(filename))
        
    def start(self, seed, maxdeg, maxterm, doEqts, doIeqs):
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
        deg = Miscs.getAutoDeg(maxdeg, maxterm, len(maxvars))

        logger.info("check reachability")
        dinvs, traces, inps = self.prover.checkReach()
        if not traces:
            return dinvs

        _f = lambda mlocs: "{} locs: {}".format(
            len(mlocs), ', '.join(map(str, mlocs)))

        def _gen(typ):
            cls = GenEqts if typ == 'eqts'else GenIeqs
            logger.info("gen {} at {}".format(typ, _f(traces.keys())))         
            invs = cls(self.invdecls, self.prover).gen(deg, traces, inps)
            if invs:
                dinvs.merge(invs)
                logger.info("{} invs:\n{}".format(invs.siz, invs))                
            
        if doEqts: _gen('eqts')
        if doIeqs: _gen('ieqs')        
            
        logger.info("final test {} invs on all traces".format(dinvs.siz))
        dinvs = dinvs.testTraces(traces, self.invdecls)
        
        logger.info("find uniq invs")
        dinvs_ = DInvs()
        for loc in dinvs:
            invs = self.reduce([inv.inv for inv in dinvs[loc]])
            if invs:
                dinvs_[loc] = Invs(map(Inv, invs))

        ndiff =dinvs.siz - dinvs_.siz
        if ndiff:
            logger.info("removed {} redundant invs".format(ndiff))
                    

        dinvs = dinvs_
        logger.info("got {} invs, {} inps (test {}): \n{}"
                    .format(dinvs.siz, len(inps), sage.all.randint(0,100),
                            dinvs))
        return dinvs



    def reduce(self, ps):
        if len(ps) <= 1:
            return ps

        from smt_z3py import SMT_Z3

        #Remove "longer" property first (i.e. those with more variables)
        #ps = sorted(ps, reverse=True, key=lambda p: len(get_vars(p)))
        print ps
        rs = list(ps) #make a copy
        for p in ps:
            if p in rs:
                #note, the use of set makes things in non order
                xclude_p = CM.vsetdiff(rs,[p])

                if SMT_Z3.imply(xclude_p,p):
                    rs = xclude_p
        return rs
        




        
