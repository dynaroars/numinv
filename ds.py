import vu_common as CM
from sageutil import is_sage_expr
import miscs
import settings
logger = CM.VLog('ds')
logger.level = settings.logger_level  

"""
Data structures
"""

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



class Trace(tuple):
    valMaxV = 10000
    inpMaxV = 1000

    filterTrace = True
    def valOk(self):
        if self.filterTrace:
            maxV = self.valMaxV
            minV = -1 * self.valMaxV
            return all(minV <= v <= maxV for v in self)
        else:
            return True
    
    @classmethod
    def parse(cls, tracefile):
        """
        parse trace for new traces
        """
        assert isinstance(tracefile, str), tracefile        

        traces = DTraces()
        for l in CM.iread_strip(tracefile):
            #l22: 8460 16 0 1 16 8460
            parts = l.split(':')
            assert len(parts) == 2
            lineno = parts[0].strip()  #l22
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

    def __str__(self, printDetails=False):
        if printDetails:
            return ", ".join(map(str, sorted(self)))
        else:
            return str(len(self))


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

    def __str__(self, printDetails=False):
        return "\n".join("{}: {}".format(loc, traces.__str__(printDetails))
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
    def __str__(self, printStat=False):
        return ", ".join(map(lambda inv: inv.__str__(printStat), sorted(self)))

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

    @classmethod
    def mk(cls, invs):
        newInvs = Invs()
        for inv in invs:
            assert isinstance(inv, Inv)
            newInvs.add(inv)
        return newInvs
    
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

    @classmethod
    def mk(cls, loc, invs):
        assert isinstance(invs, Invs)
        newInvs = DInvs()
        newInvs[loc] = invs
        return newInvs
        
    
