from collections import OrderedDict
import os.path
import sage.all

import vu_common as CM

import miscs
from src import Src
import solver

import settings
logger = CM.VLog('alg')
logger.level = settings.logger_level  

from ds import Inp, Inps, Trace, DTraces, Inv, Invs, DInvs
from prover import Prover

class Gen(object):
    def __init__(self, invdecls, prover):
        self.invdecls = invdecls
        self.prover = prover

class GenEqts(Gen):
    def __init__(self, invdecls, prover):
        super(GenEqts, self).__init__(invdecls, prover)
        
    def gen(self, deg, traces, inps):
        assert deg >= 1, deg
        assert isinstance(traces, DTraces) and traces, traces                
        assert isinstance(inps, Inps), inps

        dinvs = DInvs()
        xtraces = DTraces()
        locs = traces.keys()
        vss = dict((loc, [sage.all.var(k) for k in self.invdecls[loc]])
                   for loc in locs)
        terms = dict((loc, miscs.getTerms(vss[loc], deg)) for loc in vss)
        termIdxss = dict((loc, miscs.getTermIdxss(len(vss[loc]), deg))
                          for loc in vss)
        
        curIter = 0
        while True:
            if not locs:
                logger.debug("no new traces")
                break

            dinvs_, locsMoreTraces = self.infer(deg, locs, terms, termIdxss,
                                                traces, xtraces)
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
                newTraces = self.prover.checkRange(dinvsFalse, traces, inps,
                                                   doSafe=False)
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

            newTraces = self.prover.checkRange(dinvs, traces, inps, doSafe=False)
            _ = newTraces.update(xtraces)
            
            locs = newTraces.keys()
            
        return dinvs

    def infer(self, deg, locs, terms, termIdxss, traces, xtraces):
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
            termIdxss_ = termIdxss[loc]
            
            logger.debug("loc {}, terms {}, deg {}, traces {}".format(
                loc, len(terms_), deg, len(traces[loc])))
            try:
                esolver = solver.EqtSolver()
                invs0 = esolver.solve1(termIdxss_, traces[loc])
                
                #cache ?
                traces_ = (dict(zip(self.invdecls[loc], tracevals))
                           for tracevals in traces[loc])

                xtraces_ = None
                if loc in xtraces:
                    xtraces_ = (dict(zip(self.invdecls[loc], tracevals))
                                for tracevals in xtraces[loc])
                invs = esolver.solve(terms_, traces_, xtraces_)
                invs = esolver.refine(invs)
                for inv in invs: dinvs.add(loc, Inv(inv))
                    
            except miscs.NotEnoughTraces as ex:
                logger.info("loc {}: {}".format(loc, ex))         
                locsMoreTraces.append(loc)

        return dinvs, locsMoreTraces


class GenIeqs(Gen):
    def __init__(self, invdecls, prover):
        super(GenIeqs, self).__init__(invdecls, prover)

    def gen(self, deg, traces, inps):
        assert deg >= 1, deg
        
        Trace.filterTrace = False
        assert isinstance(traces, DTraces) and traces, traces                
        assert isinstance(inps, Inps), inps

        dinvs = DInvs()
        locs = traces.keys()

        mymaxv  = 10
        
        maxV = mymaxv
        minV = -1*maxV
        
        ubmaxV = maxV+10
        ubminV = -1*ubmaxV

        for loc in locs:
            ieqs = self.genLoc(deg, loc, traces, inps, minV, maxV, ubminV, ubmaxV)
            dinvs[loc] = ieqs

        return dinvs

    def genLoc(self, deg, loc, traces, inps, minV, maxV, ubminV, ubmaxV):
        assert deg >= 1, deg
        assert isinstance(traces, DTraces), traces
        assert isinstance(inps, Inps), inps

        vs = [sage.all.var(k) for k in self.invdecls[loc]]
        terms = solver.getTermsFixedCoefs(vs, 1)
        logger.info("{}: check upperbounds for {} terms: {}".format(
            loc, len(terms), ', '.join(map(str,terms))))
        
        octInvs = [Inv(t <= maxV) for t in terms]
        octD = OrderedDict(zip(octInvs, terms))

        octInvs = DInvs.mk(loc, Invs.mk(octInvs))
        _ = self.prover.check(octInvs, traces, inps, ubminV, ubmaxV, doSafe=True)
        octInvs = octInvs.removeDisproved()

        if not octInvs: return invs #no nontrivial invs
        
        logger.info("{}: compute upperbounds for {} terms: {}".format(
            loc, len(octInvs[loc]),
            ', '.join(map(str, [octD[inv] for inv in octInvs[loc]]))))

        invs = Invs()
        for octInv in octInvs[loc]:            
            traces_ = (dict(zip(self.invdecls[loc], tracevals))
                       for tracevals in traces[loc])
            octTerm = octD[octInv]
            ts = [octTerm.subs(tc) for tc in traces_]
            try:
                mminV = max(t for t in ts if t < maxV)
                mminV = max(mminV, minV)
            except ValueError:
                mminV = minV

            logger.debug("refine {} (compute ub for '{}', start w/ min {}, maxV {})"
                        .format(octInv, octTerm, mminV, maxV))

            disproves = set()
            boundV = self.guessCheck(loc, octTerm, traces, inps, 
                                     mminV, maxV, ubminV, ubmaxV, disproves)
            if boundV not in disproves and boundV not in {maxV, minV}:
                inv = Inv(octTerm <= boundV)
                logger.debug("got {}".format(inv))
                invs.add(inv)

        if invs:
            logger.info("{}: found {} ieqs: {}".format(loc, len(invs), invs))

        return invs
    
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
            cexs = self.prover.check(inv_, traces, inps, ubMinV, ubMaxV, doSafe=True)
            if loc in cexs:
                assert cexs[loc]
                disproves.add(minV)
                return maxV
            else:
                # assert len(inv_[loc]) == 1
                # if list(inv_[loc])[0].isProved: proved.add(minV)
                return minV

        v = sage.all.ceil((maxV + minV)/2.0)
        inv = Inv(term <= v)
        inv_ = DInvs.mk(loc, Invs.mk([inv]))
        cexs = self.prover.check(inv_, traces, inps, ubMinV, ubMaxV, doSafe=True)

        if loc in cexs: #disproved
            assert cexs[loc]
            disproves.add(v)
            traces_ = (dict(zip(self.invdecls[loc], tracevals))
                       for tracevals in cexs[loc])
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
        self.filename = filename
        basename = os.path.basename(self.filename)
        src = os.path.join(tmpdir, basename)
        _, rs_err = CM.vcmd("astyle -Y < {} > {}".format(self.filename, src))
        assert not rs_err, rs_err
        logger.debug("src: {}".format(src))
        src = Src(src)
        self.inpdecls, self.invdecls = src.parse()
        
        printfSrc = src.instrPrintfs(self.invdecls)
        exeFile = "{}.exe".format(printfSrc)
        #-lm for math.h to work
        cmd = "gcc -lm {} -o {}".format(printfSrc, exeFile) 
        CM.vcmd(cmd)
        tcsFile =  "{}.tcs".format(printfSrc) #tracefile

        self.prover = Prover(src, exeFile,
                             self.inpdecls, self.invdecls, tcsFile, tmpdir)
        
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
        deg = miscs.getAutoDeg(maxdeg, maxterm, len(maxvars))

        logger.info("check reachability")
        dinvs, traces, inps = self.prover.checkReach()
        if not traces:
            return dinvs

        _f = lambda mlocs: "{} locs: {}".format(
            len(mlocs), ', '.join(map(str, mlocs)))
            
        if doEqts:
            logger.info("gen eqts at {}".format(_f(traces.keys())))            
            eqts = GenEqts(self.invdecls, self.prover).gen(deg, traces, inps)
            dinvs.merge(eqts)


        if doIeqs:
            logger.info("infer ieqs at {}".format(_f(traces.keys())))
            ieqs = GenIeqs(self.invdecls, self.prover).gen(deg, traces, inps)
            dinvs.merge(ieqs)

        logger.info("final test {} invs on all traces".format(dinvs.siz))
        dinvs = dinvs.testTraces(traces, self.invdecls)
        
        logger.info("got {} invs in total (test {}): \n{}"
                    .format(dinvs.siz, sage.all.randint(0,100),
                            dinvs))
                    
        return dinvs

    




        
