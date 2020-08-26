; Cycling through 3 values a, b, c.

(set-logic BV)

(define-fun hd21 ((x (BitVec 64)) (a (BitVec 64)) (b (BitVec 64)) (c (BitVec 64))) (BitVec 64)
(bvxor (bvxor (bvand (bvneg (= x c)) (bvxor a c)) (bvand (bvneg (= x a)) (bvxor b c))) c))

(synth-fun f ((x (BitVec 64)) (a (BitVec 64)) (b (BitVec 64)) (c (BitVec 64))) (BitVec 64)
		   
((Start (BitVec 64)
((bvnot Start)
(bvxor Start Start)
(bvand Start Start)
(bvor Start Start)
(bvneg Start)
(bvadd Start Start)
(bvmul Start Start)
(bvudiv Start Start)
(bvurem Start Start)
(bvlshr Start Start)
(bvashr Start Start)
(bvshl Start Start)
(bvsdiv Start Start)
(bvsrem Start Start)
(bvsub Start Start)
x
m
k
#x0000000000000000
#x0000000000000001
#x000000000000001f
#xffffffffffffffff
(ite StartBool Start Start)))
(StartBool Bool
((= Start Start)))))

(declare-var x (BitVec 64))
(declare-var a (BitVec 64))
(declare-var b (BitVec 64))
(declare-var c (BitVec 64))

(constraint (= (hd21 x a b c) (f x a b c)))
(check-synth)

