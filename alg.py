#Todo 1: parallelize equations (should speed up lcm etc)
#Todo 2: eqts, after generate candidates first time, check them against init traces
#then add the cex traces to exprs
#Todo 4: no need to exclude inps when checking inv

from collections import OrderedDict
import os.path
import sage.all

import vu_common as CM

from miscs import Miscs, Template
from src import Src

import settings
logger = CM.VLog('alg')
logger.level = settings.logger_level  
logger.printtime = settings.logger_printtime

from ds import Inp, Inps, Traces, DTraces, Inv, Invs, DInvs
from prover import Prover

class Gen(object):
    def __init__(self, invdecls, prover):
        self.invdecls = invdecls
        self.prover = prover

class GenEqts(Gen):
    def __init__(self, invdecls, prover):
        super(GenEqts, self).__init__(invdecls, prover)

    def getInitTraces(self, loc, deg, traces, inps, rate=1.5):
        vs = tuple(self.invdecls[loc])
        
        terms = Miscs.getTerms([sage.all.var(k) for k in vs], deg)
        template, uks = Template.mk(terms, 0, retCoefVars=True)
        nEqtsNeeded = int(rate * len(uks))
        traces_ = [tc.mydict(vs) for tc in traces[loc]]
        exprs = template.instantiateTraces(traces_, nEqtsNeeded)

        while nEqtsNeeded > len(exprs):
            logger.debug("{}: need more traces ({} eqts, need >= {})"
                         .format(loc, len(exprs), nEqtsNeeded))
            dinvsFalse = DInvs.mkFalses([loc])
            dTraces, _ = self.prover.checkRange(
                dinvsFalse, traces, inps, doSafe=False, doExec=True)
            
            if loc not in dTraces:
                logger.warn("{}: cannot generate enough traces".format(loc))
                return
                
            traces_ = [tc.mydict(vs) for tc in dTraces[loc]]
            logger.debug("obtain {} new traces".format(len(traces_)))
            newExprs = template.instantiateTraces(traces_,
                                                  nEqtsNeeded - len(exprs))
            for expr in newExprs:
                assert expr not in exprs
                exprs.add(expr)
                
        return template, uks, exprs

    @classmethod
    def refine(cls, sols):
        if not sols: return sols
        sols = Miscs.reduceEqts(sols)
        sols = [Miscs.elimDenom(s) for s in sols]
        #don't allow large coefs
        sols_ = []
        for s in sols:
            if any(abs(c) > 20 for c in Miscs.getCoefs(s)):
                logger.detail("large coefs: ignore {}".format(s))
            else:
                sols_.append(s)
        sols = sols_
        return sols        

    @classmethod
    def solve(cls, eqts, uks, template):
        logger.debug("solve {} uks using {} eqts".format(len(uks), len(eqts)))
        rs = sage.all.solve(eqts, uks, solution_dict=True)
        eqts = template.instantiateSols(rs)
        eqts = cls.refine(eqts)
        return eqts

        
    def infer(self, loc, template, uks, exprs, dtraces, inps):
        assert isinstance(loc, str), loc
        assert isinstance(template, Template), template
        assert isinstance(uks, list), uks
        assert isinstance(exprs, set) and exprs, exprs
        assert isinstance(dtraces, DTraces) and dtraces, dtraces
        assert isinstance(inps, Inps) and inps, inps

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
                logger.debug("{}: no new results -- break".format(loc))
                continue
                
            for p in unchecks: cache.add(p)
            logger.debug('{}: {} candidates:\n{}'.format(
                loc, len(newEqts), '\n'.join(map(str, newEqts))))

            logger.debug("{}: check {} unchecked ({} candidates)"
                         .format(loc, len(unchecks), len(newEqts)))

            dinvs = DInvs.mk(loc, Invs.mk(map(Inv, unchecks)))
            _, dCexs = self.prover.checkRange(
                dinvs, dtraces, inps, doSafe=False, doExec=False)

            _ = [eqts.add(inv) for loc in dinvs for inv in dinvs[loc]
                 if not inv.isDisproved]
            
            if loc not in dCexs:
                logger.debug("{}: no disproved candidates -- break".format(loc))
                continue
            
            newTraces = True
            cexs = Traces.extract(dCexs[loc], vs)
            exprs_ = template.instantiateTraces(cexs.mydicts, None)
            logger.debug("{}: {} new cex exprs".format(loc, len(exprs_)))
            exprs.extend(exprs_)

                     
        logger.debug("got {} eqts".format(len(eqts)))
        if eqts: logger.debug('\n'.join(map(str, eqts)))
        return eqts
                
    def gen(self, deg, traces, inps):
        assert deg >= 1, deg
        assert isinstance(traces, DTraces) and traces, traces                
        assert isinstance(inps, Inps), inps

        #first obtain enough traces
        initrs = [self.getInitTraces(loc, deg, traces, inps) for loc in traces]
        initrs = [(loc, rs) for loc, rs in zip(traces, initrs) if rs]
        
        #then solve/prove in parallel
        dinvs = DInvs()
        for loc, rs in initrs:
            template, uks, exprs = rs
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

        #without these restrictions, klee takes a long time to run
        ubmaxV = maxV*2
        ubminV = -1*ubmaxV

        locs = traces.keys()
        vss = [[sage.all.var(k) for k in self.invdecls[loc]]  for loc in locs]
        termss = [Miscs.getTermsFixedCoefs(vs, 2) for vs in vss]
        logger.info("{} locs: check upperbounds for {} terms".format(
            len(locs), sum(map(len, termss))))
        
        refs = {loc: {Inv(t <= maxV): t for t in terms}
                for loc, terms in zip(locs, termss)}
        ieqs = DInvs((loc, Invs.mk(refs[loc].keys())) for loc in refs)
        #TODO, if take too long then use this
        _ = self.prover.check(ieqs, traces, inps, ubminV, ubmaxV, doSafe=True, doExec=True) #
        #_ = self.prover.checkRange(ieqs, traces, inps, doSafe=True, doExec=True) #
        
        ieqs = ieqs.removeDisproved()

        tasks = [(loc, refs[loc][ieq]) for loc in ieqs for ieq in ieqs[loc]]

        logger.info("{} locs: compute upperbounds for {} terms".format(
            len(locs), len(tasks)))
        
        def _f(loc, term):
            vs = traces[loc].myeval(term)
            try:
                mminV = int(max(minV, max(v for v in vs if v < maxV)))
            except ValueError:
                mminV = minV
                
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

        do_parallel = settings.doMP and len(tasks) >= 2
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

    def guessCheck(self, loc, term, traces, inps, minV, maxV,
                   ubMinV, ubMaxV, disproves):
        assert minV <= maxV, (minV, maxV, term)
        assert ubMinV < ubMaxV, (ubMinV, ubMaxV)
        assert isinstance(traces, DTraces), traces
        assert isinstance(disproves, set), disproveds

        #print term, minV, maxV, ubMinV, ubMaxV
        if minV == maxV: return maxV
        elif maxV - minV == 1:
            if minV in disproves:
                return maxV
            inv = Inv(term <= minV)
            inv_ = DInvs.mk(loc, Invs.mk([inv]))
            _, dCexs = self.prover.check(
                inv_, traces, inps, ubMinV, ubMaxV, doSafe=True, doExec=False)

            if loc in dCexs:
                assert dCexs[loc]
                disproves.add(minV)
                return maxV
            else:
                return minV

        v = sage.all.ceil((maxV + minV)/2.0)
        inv = Inv(term <= v)
        inv_ = DInvs.mk(loc, Invs.mk([inv]))
        _, dCexs = self.prover.check(
            inv_, traces, inps, ubMinV, ubMaxV, doSafe=True, doExec=False)
            
        if loc in dCexs: #disproved
            assert dCexs[loc]            
            cexs = Traces.extract(dCexs[loc], tuple(self.invdecls[loc]), useOne=False)
            minV = int(max(cexs.myeval(term)))
            disproves.add(v)
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
        self.tmpdir = tmpdir
        self.filename = filename
        logger.info("analyze {}".format(filename))
        
    def start(self, seed, maxdeg, maxterm, doEqts, doIeqs):
        assert isinstance(seed, (int,float)), seed
        assert isinstance(doEqts, bool), doEqts
        assert isinstance(doIeqs, bool), doIeqs

        from time import time
        st = time()
        
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

        def strOfLocs(locs):
            _f = lambda vts: ', '.join("{} {}".format(vts[v], v) for v in vts)
            s = '; '.join("{} ({})".format(
                loc, _f(self.invdecls[loc])) for loc in locs)
            return "{} locs: {}".format(len(locs), s)
            
        def _gen(typ):
            cls = GenEqts if typ == 'eqts'else GenIeqs
            logger.info("gen {} at {}".format(typ, strOfLocs(traces.keys()))) 
            invs = cls(self.invdecls, self.prover).gen(deg, traces, inps)
            if invs:
                dinvs.merge(invs)
                logger.info("{} invs:\n{}".format(dinvs.siz, dinvs))                
            
        if doEqts: _gen('eqts')
        if doIeqs: _gen('ieqs')        
            
        logger.info("test {} invs on all {} traces".format(dinvs.siz, traces.siz))
        dinvs = dinvs.testTraces(traces)
        
        logger.info("find uniq invs")
        logger.info("{} invs:\n{}".format(dinvs.siz, dinvs))
        oldSiz = dinvs.siz

        #TODO: parallel
        dinvs = [(loc, Miscs.reduceSMT([inv.inv for inv in dinvs[loc]]))
                 for loc in dinvs]
        dinvs = DInvs((loc, Invs(map(Inv, invs)))
                      for loc, invs in dinvs if invs)
        ndiff = oldSiz - dinvs.siz
        if ndiff:
            logger.info("removed {} redundant invs".format(ndiff))
                    
        logger.info("got {} invs, {} inps (test {}): \n{}"
                    .format(dinvs.siz, len(inps), sage.all.randint(0,100),
                            dinvs))

        
        logger.info("*done* prog {}, invs {}, time {} s".format(self.filename, dinvs.siz, time() - st))
        import shutil
        logger.debug("rm -rf {}".format(self.tmpdir))
        shutil.rmtree(self.tmpdir)
        
        return dinvs
