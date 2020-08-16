; Hacker's delight 01, minimal grammar
; Turn off the rightmost 1-bit in a bit-vector.

(set-logic BV)

(define-fun hd01 ((x (BitVec 64))) (BitVec 64) (bvand x (bvsub x #x0000000000000001)))

(synth-fun f ((x (BitVec 64))) (BitVec 64)
    ((Start (BitVec 64) ((bvand Start Start)
                         (bvsub Start Start)
                         x
                         #x00000001))))

(declare-var x (BitVec 64))
(constraint (= (hd01 x) (f x)))
(check-synth)

