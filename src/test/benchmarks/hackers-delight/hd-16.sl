; max of two unsigned integers (not in HD suite)

(set-logic BV)

(define-fun hd16 ((x (BitVec 64)) (y (BitVec 64))) (BitVec 64) (ite (bvslt x y) y x))

(synth-fun f ((x (BitVec 64)) (y (BitVec 64))) (BitVec 64)
((Start Bool ((bvule StartBV StartBV)
(bvult StartBV StartBV)
(bvslt StartBV StartBV)
(bvsle StartBV StartBV)
(bvugt StartBV StartBV)
(= StartBV StartBV)))

(StartBV (BitVec 64) ((bvnot StartBV)
					(bvxor StartBV StartBV)
					(bvand StartBV StartBV)
					(bvor StartBV StartBV)
					(bvneg StartBV)
					(bvadd StartBV StartBV)
					(bvmul StartBV StartBV)
					(bvudiv StartBV StartBV)
					(bvurem StartBV StartBV)
					(bvlshr StartBV StartBV)
					(bvashr StartBV StartBV)
					(bvshl StartBV StartBV)
					(bvsdiv StartBV StartBV)
					(bvsrem StartBV StartBV)
					(bvsub StartBV StartBV)
                    x
                    y
                    (ite Start StartBV StartBV)))))

(declare-var x (BitVec 64))
(declare-var y (BitVec 64))
(constraint (= (hd16 x y) (f x y)))
(check-synth)