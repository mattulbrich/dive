(declare-sort universe)
(declare-sort field)
(define-sort Heap () (Array universe field universe))

; === Types
(declare-datatypes () ((type
  ty$bool
  ty$int
  ty$object
  ty$null
  (ty$array (ty$array$param type))
  (ty$array2 (ty$array2$param type))
  (ty$set (ty$set$param type))
  <classes:{ n | class$<n>
}>)))

(declare-fun ty (universe) type)
(define-fun ty$ref ((u universe)) Bool
  (or (= (ty u) ty$null)
      (= (ty u) (ty$array (ty$array$param (ty u))))
      (= (ty u) (ty$array2 (ty$array2$param (ty u))))
      (= (ty u) ty$object)
      <classes:{ n | (= (ty u) class$<n>)
}>  )
)

; == Embedding into universe
(declare-fun u2i (universe) Int)
(declare-fun i2u (Int) universe)
(assert (forall ((i Int)) (! (= (u2i (i2u i)) i)
    :pattern ((u2i (i2u i))))))
(assert (forall ((i Int)) (= (ty (i2u i)) ty$int)))

(declare-fun u2b (universe) Bool)
(declare-fun b2u (Bool) universe)
(assert (forall ((b Bool)) (= (u2b (b2u b)) b)))
(assert (forall ((b Bool)) (= (ty (b2u b)) ty$bool)))

(declare-fun $len0 (universe) Int)
(declare-const $heap Heap)

(declare-fun $in (universe universe) Bool)

; === Heap operations

(declare-fun $anon (Heap universe Heap) Heap)
(assert (forall ((h Heap)(m universe)(h2 Heap)(o universe)(f field))
    (= (select ($anon h m h2) o f)
       (select (ite ($in o m) h2 h) o f))))

; --- Fields
(declare-fun fieldSerialNo (field) Int)

(declare-fun $arrIdx (Int) field)
(assert (forall ((i Int)) (=> (>= i 0) (= (fieldSerialNo ($arrIdx i)) i))))

<fields:{ f |
(declare-const |field$<f>| field)
(assert (= (fieldSerialNo |field$<f>|) -<i>))

}>

; === Builtin functions

(declare-const $everything universe)
(assert (forall ((u universe)) 
  (=> (ty$ref u) ($in u $everything))))


<!
;; select<C, D>  (heap, C, field<C,D>) --> D
;; select<C,D>(h, r, f)  -->
;;   (o2c$D (u2o (select h (c2o$C r) f)))
;; store<C, D> (heap, C, field<C,D>, D) --> heap
;;   (store heap (c2o$C r) f (o2u (c2o$D value)))
!>