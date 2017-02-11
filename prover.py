import os.path
from collections import OrderedDict
import time

import vu_common as CM
from miscs import Miscs

from klee import KLEE

import settings
logger = CM.VLog('prover')
logger.level = settings.logger_level  
logger.printtime = settings.logger_printtime

from ds import Inp, Inps, DTraces, Inv,  DInvs
from src import Src

def merge(ds):
    newD = {}
    for d in ds:
        for loc in d:
            assert d[loc]
            if loc not in newD: newD[loc] = {}
            for inv in d[loc]:
                assert d[loc][inv]
                if inv not in newD[loc]: newD[loc][inv] = set()
                for e in d[loc][inv]:
                    newD[loc][inv].add(e)
    return newD

class Prover(object):
    def __init__(self, src, inpdecls, invdecls,
                 exeFile, tcsFile, tmpdir):
                 
        assert isinstance(src, Src), src
        self.src = src
        self.exeFile = exeFile
        self.inpdecls = inpdecls
        self.invdecls = invdecls
        self.tmpdir = tmpdir
        self.tcsFile = tcsFile

    def getInpsSafe(self, dinvs, inps, inpsd):
        """call verifier on each inv"""
        def wprocess(tasks, Q):
            myinps = set() #inps #Faster when using few constraints
            rs = [(loc, inv,
                   self.src.instrAsserts(
                       {loc:set([inv])}, myinps, inpsd,self.invdecls))
                     for loc, inv in tasks]
            rs = [(loc, inv, KLEE(isrc, self.tmpdir).getDInps())
                  for loc, inv, isrc in rs]
            if Q is None: #no multiprocessing
                return rs
            else:
                Q.put(rs)

        tasks = [(loc, inv) for loc in dinvs for inv in dinvs[loc]
                 if inv.stat is None]
        do_parallel = len(tasks) >= 2
        myrefs = dict(((loc, str(inv)), inv) for loc,inv in tasks)

        if do_parallel:
            from vu_common import get_workloads
            from multiprocessing import (Process, Queue, 
                                         current_process, cpu_count)
            Q=Queue()
            workloads = get_workloads(tasks, 
                                      max_nprocesses=cpu_count(),
                                      chunksiz=2)

            logger.debug("workloads 'prove' {}: {}"
                         .format(len(workloads),map(len,workloads)))

            workers = [Process(target=wprocess,args=(wl,Q))
                       for wl in workloads]

            for w in workers: w.start()
            wrs = []
            for _ in workers: wrs.extend(Q.get())
        else:
            wrs = wprocess(tasks, Q=None)

        #merge results
        newInps = Inps()
        mInps, mCexs = [], []
        for loc, inv, (klDInps, klDCexs, isSucc) in wrs:
            mInps.append(klDInps)
            mCexs.append(klDCexs)
            rinv = myrefs[loc, str(inv)]
            try:                    
                klInps = klDInps[loc][str(inv)]
                rinv.stat = Inv.DISPROVED
            except KeyError:
                rinv.stat = Inv.PROVED if isSucc else Inv.UNKNOWN

        assert all(inv.stat is not None
                   for loc in dinvs for inv in dinvs[loc])

        mInps = merge(mInps)
        mCexs = merge(mCexs)
        return mInps, mCexs

    def getInpsUnsafe(self, dinvs, inps, inpsd):
        """
        call verifier on all invs
        """
        
        dinvs_ = DInvs()
        _ = [dinvs_.add(loc, inv) for loc in dinvs
             for inv in dinvs[loc] if inv.stat is None]
        klSrc = self.src.instrAsserts(dinvs_, inps, inpsd, self.invdecls)
        klDInps, klDCexs, _ = KLEE(klSrc, self.tmpdir).getDInps()

        #IMPORTANT: getDInps() returns an isSucc flag (false if timeout),
        #but it's not useful here (when haveing multiple klee_asserts)
        #because even if isSucc, it doesn't guarantee to generate cex
        #for a failed assertions (that means we can't claim if an assertion
        #without cex is proved).
        newInps = Inps()
        for loc in dinvs:
            for inv in dinvs[loc]:
                if inv.stat is not None: continue
                try:
                    sinv = str(inv)
                    klInps = klDInps[loc][sinv]
                    inv.stat = Inv.DISPROVED
                except KeyError:
                    pass
        return klDInps, klDCexs
    
    def getInps(self, dinvs, inps, minV, maxV, doSafe):
        """
        return new inps (and also add them to inps)
        """
        assert isinstance(dinvs, DInvs) and dinvs.siz, dinvs
        assert minV < maxV, (minV, maxV)
        assert isinstance(inps, Inps), inps        
        assert isinstance(doSafe, bool), doSafe

        if self.inpdecls:
            inpsd = OrderedDict((vname, (vtyp, (minV, maxV)))
                                for vname, vtyp in self.inpdecls.iteritems())
        else:
            inpsd = None

        _f = self.getInpsSafe if doSafe else self.getInpsUnsafe
        dInps, dCexs = _f(dinvs, inps, inpsd)

        newInps = (Inp(inp) for loc in dInps
                    for inv in dInps[loc]
                    for inp in dInps[loc][inv])
        
        newInps = Inps(inp for inp in newInps if inp not in inps)        
        for inp in newInps: inps.add(inp)
        return newInps, dCexs

    def getTraces(self, inps):
        """
        Run program on inps and get traces
        """
        assert isinstance(inps, Inps) and inps, inps

        tcsFile = "{}_{}".format(self.tcsFile, hash(str(inps))).replace("-","_")
        if os.path.isfile(tcsFile):  #need to check for parallism
            traces = DTraces.parse(tcsFile, self.invdecls)
        else:
            for inp in inps:
                inp_ = ' '.join(map(str, inp))
                cmd = "{} {} >> {}".format(self.exeFile, inp_, tcsFile)
                logger.detail(cmd)
                CM.vcmd(cmd)
            traces = DTraces.parse(tcsFile, self.invdecls)
            
        assert all(loc in self.invdecls for loc in traces), traces.keys()
        return traces


    def check(self, dinvs, traces, inps, minv, maxv, doSafe, doExec):
        """
        Check invs.
        Also update traces, inps
        """
        assert isinstance(dinvs, DInvs), dinvs
        assert isinstance(traces, DTraces), traces
        assert isinstance(inps, Inps), inps        
        assert isinstance(doSafe, bool), doSafe
        assert isinstance(doExec, bool), doExec
        
        logger.detail("checking {} invs (doSafe {}, doExec {}):\n{}".format(
            dinvs.siz, doSafe, doExec, dinvs.__str__(printStat=True)))
        dInps, dCexs = self.getInps(dinvs, inps, minv, maxv, doSafe)

        if doExec and dInps: 
            newTraces = self.getTraces(dInps)
            logger.debug("got {} traces from {} inps"
                         .format(newTraces.siz, len(dInps)))
            newTraces = newTraces.update(traces, self.invdecls)
        else:
            newTraces = DTraces()

        return newTraces, dCexs            

    def checkRange(self, dinvs, traces, inps, doSafe, doExec):
        minv, maxv = -1*DTraces.inpMaxV, DTraces.inpMaxV,         
        return self.check(dinvs, traces, inps, minv, maxv, doSafe, doExec)

    def checkNoRange(self, dinvs, traces, inps, doExec):
        minv, maxv = -1*DTraces.inpMaxV*10, DTraces.inpMaxV*10,
        doSafe=True
        return self.check(dinvs, traces, inps, minv, maxv, doSafe, doExec)

    def checkReach(self):
        #check for reachability using inv False (0)
        dinvs = DInvs.mkFalses(self.invdecls)        
        inps = Inps()

        #use some initial inps first
        rinps = Miscs.genInitInps(len(self.inpdecls), DTraces.inpMaxV)
        for inp in rinps: inps.add(Inp(inp))
        traces = self.getTraces(inps)
        unreachLocs = [loc for loc in dinvs if loc not in traces]
        if unreachLocs:
            logger.debug("use RT to generate traces for {}".format(
                ','.join(map(str, unreachLocs))))
            unreachInvs = DInvs.mkFalses(unreachLocs)
            _ = self.checkRange(unreachInvs, traces, inps, doSafe=True, doExec=True)

        #remove FALSE invs indicating unreached locs
        for loc in traces:
            assert traces[loc]
            dinvs[loc].clear()

        return dinvs, traces, inps
    
