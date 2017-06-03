import vu_common as CM
import os
import os.path
import subprocess as sp

def vcmd(cmd, inp=None, shell=True):
    proc = sp.Popen(cmd,shell=shell,stdin=sp.PIPE,stdout=sp.PIPE,stderr=sp.PIPE)
    return proc.communicate(input=inp)


def run(dir_, ntimes):
    print ("**** Run dir {} for {} times".format(dir_, ntimes))

    fs = [os.path.join(dir_, f)
          for f in os.listdir(dir_) if f.endswith(".c")]

    for f in fs:
        if not os.path.isfile(f):
            print "File {} does not exist".format(f)
            continue

        for i in range(ntimes):
            print "Running {} with seed {}".format(f, i)
            cmd = "timeout 5m $SAGE/sage -python -O dig2.py {}  -log 3 -seed {}".format(f,i)
            print cmd
            stdout, stderr = vcmd(cmd)
            print stdout
            print stderr
            

ntimes = 11
#NLA
dirNLA = "programs/nla/"
run(dirNLA, ntimes)


dirComplexity = "programs/complexity/gulwani_cav09"
run(dirComplexity, ntimes)

dirComplexity = "programs/complexity/gulwani_pldi09"
run(dirComplexity, ntimes)

dirComplexity = "programs/complexity/gulwani_popl09"
run(dirComplexity, ntimes)


# dirHola = "programs/hola/"
# run(dirHola, ntimes)

