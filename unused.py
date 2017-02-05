
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
            
