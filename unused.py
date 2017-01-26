
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
