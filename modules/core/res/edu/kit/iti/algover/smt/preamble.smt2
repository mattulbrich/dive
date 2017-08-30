(declare-sort object)
(declare-sort universe)
(declare-sort field)
(define-sort Heap () (Array object field universe))
(define-sort Set (X) (Array X Bool))

(declare-fun u2o (universe) object)
(declare-fun o2u (object) universe)
(assert (forall ((o object)) (= (u2o (o2u o)) o)))

(declare-fun u2i (universe) Int)
(declare-fun i2u (Int) universe)
(assert (forall ((i Int)) (= (u2i (i2u i)) i)))

(declare-fun u2b (universe) Bool)
(declare-fun b2u (Bool) universe)
(assert (forall ((b Bool)) (= (u2b (b2u b)) b)))

(declare-fun $len0 (object) Int)
(declare-const $heap Heap)
;(declare-const null Ref)

; === Set operations
;(define-fun ((

; === Heap operations

(declare-fun $anon (Heap (Set object) Heap) Heap)
(assert (forall ((h Heap)(m (Set object))(h2 Heap)(o object)(f field))
    (= (select ($anon h m h2) o f)
       (select (ite ($in o m) h2 h) o f)))



; === Declarations for Dafny classes ===
<classes:{ n |
; --- Class <n> ---
(declare-sort class$Name)
(declare-fun c2o$<n> (class$<n>) object)
(declare-fun o2c$<n> (object) class$<n>)
(assert (forall ((x class$<n>)) (= o2c$<n> (c2o$<n> x) x)))

}>
; === Fields
(declare-fun fieldSerialNo (field) Int)

(declare-fun $arrIdx (Int) field)
(assert (forall ((i Int)) (impl (>= i 0) (= (fieldSerialNo ($arrIdx i)) i))))

<fields:{ f |
(declare-const field$<f> field)
(assert (= (fieldSerialNo field$<f>) -<i>))

}>


<!
;; select<C, D>  (heap, C, field<C,D>) --> D
;; select<C,D>(h, r, f)  -->
;;   (o2c$D (u2o (select h (c2o$C r) f)))
;; store<C, D> (heap, C, field<C,D>, D) --> heap
;;   (store heap (c2o$C r) f (o2u (c2o$D value)))
!>