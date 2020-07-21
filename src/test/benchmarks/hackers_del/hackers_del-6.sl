; Turn on the right most 0 bit

; (define-fun hd06 ((x (BitVec 32))) (BitVec 32) (bvor x (bvadd x #x00000001)))

(set-logic BV)
(synth-fun f ( (x (BitVec 64)) ) (BitVec 64)
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
#x0000000000000000
#x0000000000000001
#x0000000000000002
#x0000000000000003
#x0000000000000004
#x0000000000000005
#x0000000000000006
#x0000000000000007
#x0000000000000008
#x0000000000000009
#x0000000000000009
#x0000000000000009
#x000000000000000A
#x000000000000000B
#x000000000000000C
#x000000000000000D
#x000000000000000E
#x000000000000000F
#x0000000000000010
(ite StartBool Start Start)
))
(StartBool Bool
((= Start Start)
(not StartBool)
(and StartBool StartBool)
(or StartBool StartBool)
))))

(constraint (= (f #x6bedbd49e6e3b640) #x6bedbd49e6e3b641))
(constraint (= (f #x37cc81b866519cc3) #x37cc81b866519cc7))
(constraint (= (f #x3166448e9564eb01) #x3166448e9564eb03))
(constraint (= (f #x1c5e12c8800d2c9e) #x1c5e12c8800d2c9f))
(constraint (= (f #x8ea3a7177232c706) #x8ea3a7177232c707))
(check-synth)