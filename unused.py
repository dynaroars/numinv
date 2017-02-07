
    def getInpsNoRange(self, dinvs, inps):
        minv, maxv = -1*Trace.inpMaxV*10, Trace.inpMaxV*10, 
        return self.getInps(dinvs, inps, minv, maxv, doSafe=True)


            #final check
            # logger.info("final check {} invs".format(dinvs.siz))
            # logger.detail(dinvs.__str__(printStat=True))
            # #final tests
            # dinvs.resetStats()
            # _ = self.getInpsNoRange(dinvs, inps)
            # dinvs = dinvs.removeDisproved()    


# def getTermIdxss(ns, deg):
#     assert ns >= 0, ns
#     assert deg >= 1, deg

#     ss = [None] + range(ns)
#     combs = itertools.combinations_with_replacement(ss, deg)
#     combs = [[idx for idx in idxs if idx is not None] for idxs in combs]
#     combs = [tuple(idxs) for idxs in combs if idxs]
#     return combs
            


    def gen1(self, deg, traces, inps):
        assert deg >= 1, deg
        assert isinstance(traces, DTraces) and traces, traces                
        assert isinstance(inps, Inps), inps

        dinvs = DInvs()
        xtraces = DTraces()
        locs = traces.keys()
        vss = dict((loc, [sage.all.var(k) for k in self.invdecls[loc]])
                   for loc in locs)
        terms = dict((loc, Miscs.getTerms(vss[loc], deg)) for loc in vss)
        curIter = 0
        while True:
            if not locs:
                logger.debug("no new traces ({} existing traces)"
                             .format(traces.siz))
                break

            dinvs_, locsMoreTraces = self.infer(deg, locs, terms, traces, xtraces)
                                                
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

            logger.debug("******************checking candidates********************")
            print dinvs.__str__(True)
            newTraces = self.prover.checkRange(dinvs, traces, inps,
                                               doSafe=False)
            _ = newTraces.update(xtraces)
            
            locs = newTraces.keys()
            
        return dinvs

    
    
    def infer(self, deg, locs, terms, traces, xtraces):
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
            vs = tuple(self.invdecls[loc])
            #eqtTemplate = solver.Template.mk(terms_, 0, retCoefVars=True)
            try:
                esolver = solver.EqtSolver()
                traces_ = (trace.mydict(vs) for trace in traces[loc])
                xtraces_ = None
                if loc in xtraces:
                    xtraces_ = [trace.mydict(vs) for trace in xtraces[loc]]
                invs = esolver.solve(terms_, traces_, xtraces_)
                invs = esolver.refine(invs)
                for inv in invs: dinvs.add(loc, Inv(inv))
                    
            except NotEnoughTraces as ex:
                logger.info("loc {}: {}".format(loc, ex))         
                locsMoreTraces.append(loc)

        return dinvs, locsMoreTraces

