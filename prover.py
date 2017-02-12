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
    def __init__(self, src, inpdecls, invdecls, tmpdir):
        assert isinstance(src, Src), src
        self.src = src
        self.inpdecls = inpdecls
        self.invdecls = invdecls
        self.tmpdir = tmpdir

    def getInpsSafe(self, dinvs, inps, inpsd):
        """call verifier on each inv"""
        def wprocess(tasks, Q):
            rs = [(loc, inv,
                   self.src.instrAsserts(
                       {loc:set([inv])}, inps, inpsd,self.invdecls))
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

    # def getInpsUnsafe(self, dinvs, inps, inpsd):
    #     """
    #     call verifier on all invs
    #     """
    #     dinvs_ = DInvs()
    #     _ = [dinvs_.add(loc, inv) for loc in dinvs
    #          for inv in dinvs[loc] if inv.stat is None]
    #     klSrc = self.src.instrAsserts(dinvs_, inps, inpsd, self.invdecls)
    #     klDInps, klDCexs, _ = KLEE(klSrc, self.tmpdir).getDInps()

    #     #IMPORTANT: getDInps() returns an isSucc flag (false if timeout),
    #     #but it's not useful here (when haveing multiple klee_asserts)
    #     #because even if isSucc, it doesn't guarantee to generate cex
    #     #for a failed assertions (that means we can't claim if an assertion
    #     #without cex is proved).
    #     newInps = Inps()
    #     for loc in dinvs:
    #         for inv in dinvs[loc]:
    #             if inv.stat is not None: continue
    #             try:
    #                 sinv = str(inv)
    #                 klInps = klDInps[loc][sinv]
    #                 inv.stat = Inv.DISPROVED
    #             except KeyError:
    #                 pass
    #     return klDInps, klDCexs
    
    def check(self, dinvs, inps, minv, maxv):
        """
        Check invs.
        Also update traces, inps
        """
        assert isinstance(dinvs, DInvs), dinvs
        assert inps is None or (isinstance(inps, Inps) and inps), inps        
        
        if self.inpdecls:
            inpsd = OrderedDict((vname, (vtyp, (minv, maxv)))
                                for vname, vtyp in self.inpdecls.iteritems())
        else:
            inpsd = None
            
        logger.detail("checking {} invs:\n{}".format(
            dinvs.siz, dinvs.__str__(printStat=True)))
        return self.getInpsSafe(dinvs, inps, inpsd)

    def checkRange(self, dinvs, inps):
        minv, maxv = -1*DTraces.inpMaxV, DTraces.inpMaxV,         
        return self.check(dinvs, inps, minv, maxv)

    def checkNoRange(self, dinvs, traces, inps):
        minv, maxv = -1*DTraces.inpMaxV*10, DTraces.inpMaxV*10,
        return self.check(dinvs, inps, minv, maxv)

