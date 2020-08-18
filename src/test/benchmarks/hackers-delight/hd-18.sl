; determine if power of two

(set-logic BV)

(define-fun hd18 ((x (BitVec 64))) Bool (and (not (bvredor (bvand (bvsub x #x0000000000000001) x))) (bvredor x)))

(synth-fun f ( (x (BitVec 64)) ) Bool
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
x)

(StartBool Bool
((= Start Start)
(bvult Start Start)
(bvslt Start Start)
(bvsle Start Start)
(bvule Start Start)
)))))

(declare-var x (BitVec 64))
(constraint (= (hd18 x) (f x)))
(check-synth)

