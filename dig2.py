import vu_common as CM

if __name__ == "__main__":
    import argparse
    aparser = argparse.ArgumentParser("DIG2 (Dynamic Invariant Generator)")
    aparser.add_argument("inp", help="inp")
    
    #0 Error #1 Warn #2 Info #3 Debug #4 Detail
    aparser.add_argument("--logger_level", "-logger_level",
                         help="set logger info",
                         type=int,
                         choices=range(5),
                         default = 2)

    aparser.add_argument("--seed", "-seed",
                         type=float,
                         help="use this seed")
    
    aparser.add_argument("--maxdeg", "-maxdeg",
                         type=int,
                         default=None,
                         help="find nonlinear invs up to degree")

    aparser.add_argument("--maxterm", "-maxterm",
                         type=int,
                         default=None,
                         help="autodegree")

    aparser.add_argument("--noEqts", "-noEqts",
                         action="store_true")

    aparser.add_argument("--noIeqs", "-noIeqs",
                         action="store_true")

    aparser.add_argument("--ieqTyp", "-ieqTyp",
                         action="store",
                         default="oct")
    
    aparser.add_argument("--test", "-test",
                         action="store_true")
    
    #Parse it
    from time import time
    args = aparser.parse_args()
    
    import settings
    settings.logger_level = args.logger_level
    logger = CM.VLog("dig2")
    logger.level = settings.logger_level

    if __debug__: logger.warn("DEBUG MODE ON. Can be slow !")
    seed = round(time(), 2) if args.seed is None else float(args.seed)

    import alg

    
    #Run it
    st = time()
    dig2 = alg.DIG2(args.inp)
    invs = dig2.start(seed=seed, maxdeg=args.maxdeg, maxterm=args.maxterm,
                      doEqts=not args.noEqts, doIeqs=not args.noIeqs,
                      ieqTyp=args.ieqTyp)
    logger.info("time {}s".format(time() - st))
    
