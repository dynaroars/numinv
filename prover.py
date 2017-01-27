import os.path
from collections import OrderedDict
import time

import vu_common as CM
import miscs

from klee import KLEE

import settings
logger = CM.VLog('prover')
logger.level = settings.logger_level  

from ds import Inp, Inps, Trace, DTraces, Inv,  DInvs
from src import Src

class Prover(object):
    def __init__(self, src, exeFile,
                 inpdecls, invdecls, tcsFile, tmpdir):
        assert isinstance(src, Src), src
        self.src = src
        self.exeFile = exeFile
        self.inpdecls = inpdecls
        self.invdecls = invdecls
        self.tmpdir = tmpdir
        self.tcsFile = tcsFile #todo parallel

    def addInps(self, klInps, newInps, inps):
        for inp in klInps:
            if self.inpdecls:
                assert inp and len(self.inpdecls) == len(inp)
                inp = Inp(inp)
            else:
                inp = Inp()
            #assert inp not in inps, inp
            if inp not in inps:
                inps.add(inp)
                newInps.add(inp)

    def getInpsSafe(self, dinvs, inps, inpsd):
        """call verifier on each inv"""
            
        tasks = [(loc, inv) for loc in dinvs for inv in dinvs[loc]
                 if inv.stat is None]

        do_parallel = len(tasks) >= 2
        myrefs = dict((str(inv), inv) for _,inv in tasks)

        def wprocess(tasks, Q):
            myinps = set() #inps #Faster when using few constraints
            rs = [(loc, inv, self.src.instrAsserts({loc:set([inv])}, myinps, inpsd))
                     for loc, inv in tasks]
            rs = [(loc, inv, KLEE(isrc, self.tmpdir).getDInps())
                  for loc, inv, isrc in rs]

            if Q is None: #no multiprocessing
                return rs
            else:
                Q.put(rs)

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
        for loc, inv, (klDInps, isSucc) in wrs:
            rinv = myrefs[str(inv)]
            try:                    
                klInps = klDInps[loc][str(inv)]
                self.addInps(klInps, newInps, inps)
                rinv.stat = Inv.DISPROVED
            except KeyError:
                rinv.stat = Inv.PROVED if isSucc else Inv.UNKNOWN

        assert all(inv.stat is not None
                   for loc in dinvs for inv in dinvs[loc])

        return newInps

    def getInpsUnsafe(self, dinvs, inps, inpsd):
        """
        call verifier on all invs
        """                
        dinvs_ = DInvs()
        for loc, invs in dinvs.iteritems():
            for inv in invs:
                if inv.stat is None:
                    dinvs_.add(loc, inv)

        klSrc = self.src.instrAsserts(dinvs_, inps, inpsd)
        klDInps, _ = KLEE(klSrc, self.tmpdir).getDInps()

        #IMPORTANT: getDInps() returns an isSucc flag (false if timeout),
        #but it's not useful here (when haveing multiple klee_asserts)
        #because even if isSucc, it doesn't guarantee to generate cex
        #for a failed assertions (that means we can't claim if an assertion
        #without cex is proved).
        newInps = Inps()
        for loc, invs in dinvs.iteritems():
            for inv in invs:
                if inv.stat is not None: continue
                try:
                    klInps = klDInps[loc][str(inv)]
                    self.addInps(klInps, newInps, inps)
                    inv.stat = Inv.DISPROVED
                except KeyError:
                    pass
        return newInps
    
    def getInps(self, dinvs, inps, minV, maxV, doSafe):
        """
        return new inps (and also add them to inps)
        """
        assert isinstance(dinvs, DInvs), dinvs
        assert minV < maxV, (minV, maxV)
        assert isinstance(dinvs, DInvs), dinvs
        assert isinstance(inps, Inps), inps        
        assert isinstance(doSafe, bool), doSafe

        if self.inpdecls:
            inpsd = OrderedDict((vname, (vtyp, (minV, maxV)))
                                for vname, vtyp in self.inpdecls.iteritems())
        else:
            inpsd = None

        if doSafe:
            return self.getInpsSafe(dinvs, inps, inpsd)
        else:
            return self.getInpsUnsafe(dinvs, inps, inpsd)

        return newInps    

    def getTraces(self, inps):
        """
        Run program on inps and get traces
        """
        assert isinstance(inps, Inps) and inps, inps

        tcsFile = "{}_{}".format(self.tcsFile, hash(str(inps))).replace("-","_")
        print tcsFile
        assert not os.path.isfile(tcsFile)
        
        for inp in inps:
            inp_ = ' '.join(map(str, inp))
            cmd = "{} {} >> {}".format(self.exeFile, inp_, tcsFile)
            logger.detail(cmd)
            CM.vcmd(cmd)

        traces = Trace.parse(tcsFile)
        assert all(loc in self.invdecls for loc in traces), traces.keys()
        return traces


    def check(self, dinvs, traces, inps, minv, maxv, doSafe):
        """
        Check invs.
        Also update traces, inps
        """
        assert isinstance(dinvs, DInvs), dinvs
        assert isinstance(inps, Inps), inps        
        assert isinstance(doSafe, bool), doSafe
        
        logger.detail("checking {} invs:\n{}".format(
            dinvs.siz, dinvs.__str__(printStat=True)))
        newInps = self.getInps(dinvs, inps, minv, maxv, doSafe)
        
        if not newInps:
            return DTraces()

        newTraces = self.getTraces(newInps)
        logger.debug("got {} traces from {} inps"
                     .format(newTraces.siz, len(newInps)))
        newTraces = newTraces.update(traces)
        return newTraces

    def checkRange(self, dinvs, traces, inps, doSafe):
        minv, maxv = -1*Trace.inpMaxV, Trace.inpMaxV,         
        return self.check(dinvs, traces, inps, minv, maxv, doSafe)

    def checkNoRange(self, dinvs, traces, inps):
        minv, maxv = -1*Trace.inpMaxV*10, Trace.inpMaxV*10, 
        return self.check(dinvs, traces, inps, minv, maxv, doSafe=True)

    def checkReach(self):
        #check for reachability using inv False (0)
        dinvs = DInvs.mkFalses(self.invdecls)        
        inps = Inps()

        #use some initial inps first
        rinps = miscs.genInitInps(len(self.inpdecls), Trace.inpMaxV)
        for inp in rinps: inps.add(Inp(inp))
        traces = self.getTraces(inps)
        unreachLocs = [loc for loc in dinvs if loc not in traces]
        if unreachLocs:
            logger.debug("use RT to generate traces for {}".format(
                ','.join(map(str, unreachLocs))))
            unreachInvs = DInvs.mkFalses(unreachLocs)
            _ = self.checkRange(unreachInvs, traces, inps, doSafe=True)

        #remove FALSE invs indicating unreached locs
        for loc in traces:
            assert traces[loc]
            dinvs[loc].clear()

        return dinvs, traces, inps
    
