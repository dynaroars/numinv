**NOTE**: This repo is for the NumInv tool, which uses the **KLEE** symbolic execution tool to check and generate counterexample inputs for invariants in **C** programs.  A new version of the work (but does not use KLEE) is available at https://github.com/unsat/dig/. This new version supports both *C* and *Java* programs. 


DIG2 (or NumInv) is a tool for generating numerical invariants using the KLEE symbolic execution tool. 
## Setup ##


DIG2 is written in Python using the SAGE mathematics system. Candidate invariants are checked using KLEE. Other verification tasks are done using the Z3 SMT solver. The tool has been tested using the following setup:

* Debian Linux 8 (64 bit)
* SageMath 7.5.1 
* Microsoft Z3 SMT solver 4.5.x
* KLEE 1.3.0.0 


### Obtain DIG2 ###
```
git clone https://github.com/unsat/numinv.git 
```

### Installing SAGE and Z3###
* Setup SAGE: download a precompiled [SageMath](http://www.sagemath.org/) binary
* Setup Z3: [download](https://github.com/Z3Prover/z3/releases) and build Z3 by following the instructions in the README file 

#### Installing KLEE  ###
* Build KLEE using these [instructions](http://klee.github.io/build-llvm34/)
* **Important**: build KLEE with Z3 support !

```
#!shell

#command to build klee
cmake -DENABLE_SOLVER_Z3=ON -DENABLE_SOLVER_STP=OFF -DENABLE_POSIX_RUNTIME=ON -DENABLE_KLEE_UCLIBC=ON  -DENABLE_UNIT_TESTS=OFF -DENABLE_SYSTEM_TESTS=OFF -DKLEE_UCLIBC_PATH=/home/tnguyen/Src/Devel/KLEE/klee-uclibc /home/tnguyen/Src/Devel/KLEE/klee
```

### Setup Paths ###
* Put the following in your `~/.bash_profile`.  Adjust the directory paths to the ones you used.
```
#!shell
# ~/.bash_profile
export Z3=PATH/TO/z3   #Z3 dir
export SAGE=PATH/TO/sage  #where your SAGE dir is
export SAGE_PATH=$Z3/src/api/python
export KLEE=$DEVEL/KLEE/
export PATH=$KLEE/klee_build_dir/bin:$SAGE:$PATH
```
*  Make sure SAGE works, e.g., use `sage` to run the SAGE interpreter or `sage --help`
*  Make sure Z3 is installed correctly so that you can do `sage -c "import z3"` without error.
*  Make sure KLEE works, e.g., `klee --help | grep z3' should say something that Z3 is the default solver

### Other miscs installations ###
* astyle: do a `apt-get install astyle`


## Usage ##
Here are some usage examples of DIG2.  The following assumes we are currently in the `dig2` directory.

### Generating invariants ###
```
#!shell
$ sage -python -O dig2.py programs/nla/cohendiv.c 
15:47:38:alg:Info:analyze programs/nla/cohendiv.c
15:47:38:alg:Info:set seed to: 1495658857.7 (test 12)
15:47:38:miscs:Info:autodeg 3
15:47:38:alg:Info:check reachability
15:47:38:alg:Info:gen eqts at 2 locs: l37 (int x, int y, int r, int q, int a, int b); l25 (int x, int y, int q, int a, int b, int r)
15:48:4:alg:Info:gen eqts: (25.3289949894s)
15:48:4:alg:Info:4 invs:
l37: a*y - b == 0, q*y + r - x == 0
l25: a*y - b == 0, q*y + r - x == 0
15:48:4:alg:Info:gen ieqs at 2 locs: l37 (int x, int y, int r, int q, int a, int b); l25 (int x, int y, int q, int a, int b, int r)
15:48:4:alg:Info:2 locs: check upperbounds for 144 terms (range 10)
15:48:25:alg:Info:gen ieqs: (21.7538409233s)
15:48:25:alg:Info:63 invs:
l37: -r - y <= -1, b - x <= 0, -b - r <= -1, -q - r <= -1, -r - x <= -1, -a - x <= -1, q - x <= 0, -r <= 0, a - x <= 0, -q - x <= -1, -a - y <= -2, a - b <= 0, r - x <= 0, r - y <= -1, -b <= 0, a - q <= 0, -q <= 0, -a - q <= 0, -y <= -1, -x <= -1, -a - b <= 0, -a - r <= -1, -b - q <= 0, -b - y <= -2, -a <= 0, -x - y <= -2, -b - x <= -1, -q - y <= -2, a*y - b == 0, q*y + r - x == 0
l25: a - x <= 0, -b + y <= 0, -r <= -1, -r - x <= -2, q - x <= -1, -a - y <= -2, -b - x <= -2, -q - y <= -1, -b - q <= -1, b - r <= 0, -x - y <= -2, a - r <= 0, a - b <= 0, -a <= -1, -b <= -1, -a - b <= -2, -b - y <= -2, -r + y <= 0, -q <= 0, -x <= -1, -q - x <= -1, r - x <= 0, -x + y <= 0, -a - x <= -2, -b - r <= -2, -q - r <= -1, -r - y <= -2, b - x <= 0, -a - q <= -1, -a - r <= -2, -y <= -1, a*y - b == 0, q*y + r - x == 0
15:48:25:alg:Info:test 63 invs on all 1622 traces
15:48:29:alg:Info:find uniq invs
15:48:29:alg:Info:63 invs:
l37: -r - y <= -1, b - x <= 0, -b - r <= -1, -q - r <= -1, -r - x <= -1, -a - x <= -1, q - x <= 0, -r <= 0, a - x <= 0, -q - x <= -1, -a - y <= -2, a - b <= 0, r - x <= 0, r - y <= -1, -b <= 0, a - q <= 0, -q <= 0, -a - q <= 0, -y <= -1, -x <= -1, -a - b <= 0, -a - r <= -1, -b - q <= 0, -b - y <= -2, -a <= 0, -x - y <= -2, -b - x <= -1, -q - y <= -2, a*y - b == 0, q*y + r - x == 0
l25: a - x <= 0, -b + y <= 0, -r <= -1, -r - x <= -2, q - x <= -1, -a - y <= -2, -b - x <= -2, -q - y <= -1, -b - q <= -1, b - r <= 0, -x - y <= -2, a - r <= 0, a - b <= 0, -a <= -1, -b <= -1, -a - b <= -2, -b - y <= -2, -r + y <= 0, -q <= 0, -x <= -1, -q - x <= -1, r - x <= 0, -x + y <= 0, -a - x <= -2, -b - r <= -2, -q - r <= -1, -r - y <= -2, b - x <= 0, -a - q <= -1, -a - r <= -2, -y <= -1, a*y - b == 0, q*y + r - x == 0
15:48:30:alg:Info:*** programs/nla/cohendiv.c, 2 locs, invs 14, inps 234, time 52.1688649654 s, rand 16: 
l37: a - q <= 0, q*y + r - x == 0, -b <= 0, r - y <= -1, -r <= 0, -a - r <= -1, a*y - b == 0
l25: -b + y <= 0, q*y + r - x == 0, a - b <= 0, b - r <= 0, -a - y <= -2, r - x <= 0, a*y - b == 0


```

Here DIG3 discovers the equality invariants `a*y = b, q*y + r = x` and other inequalities at the locations marked with `//%%%traces` from the program `programs/nla/cohenDiv.c` below:
```
#!C

int cohendiv(int x, int y){
  //Cohen's integer division that returns x % y
  assert(x>0 && y>0);
  int q=0; 
  int r=x;
  while(1){
    if (!(r>=y)) break;
    int a=1; 
    int b=y;
    while(1){
      //traces: int q, int r, int a, int b, int x, int y
      if (!(r >= 2*b)) break;
      a = 2*a;
      b = 2*b;
    }
    r=r-b;
    q=q+a;
  }
  //%%%traces: int q, int r, int a, int b, int x, int y
  return q;
}
```

### Other programs
The directory `../programs/nla/` contains many programs having such nonlinear invariants.


## Publications ##
Additional information on DIG can be found from these papers:
* ThanhVu Nguyen, Timos Antopoulos, Andrew Ruef, and Michael Hicks. A Counterexample-guided Approach to Finding Numerical Invariants. In Foundations of Software Engineering (FSE), page (to appear). ACM, 2017

## Others ##
* Benchmarks are in subdirectory "programs"  (nla, complexity, and hola)
* Results are in "**fse17_results**".  These are logs, which we use collect_results.py to extract stats such as mean #'s of invs, time, etc
