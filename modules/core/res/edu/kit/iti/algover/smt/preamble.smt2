(declare-sort universe)
(declare-sort field)
(define-sort Heap () (Array universe field universe))

; === Types
(declare-datatypes () ((type
  ty$bool
  ty$int
  ty$object
  ty$null
  ty$heap
  (ty$array (ty$array$param type))
  (ty$array2 (ty$array2$param type))
  (ty$set (ty$set$param type))
  <classes:{ n | class$<n>
}>)))

(declare-fun ty (universe) type)

(declare-fun isA (universe type) Bool)
(assert (forall ((u universe)) (! (= (isA u ty$bool) (= (ty u) ty$bool)) :pattern ((isA u ty$bool)))))
(assert (forall ((u universe)) (! (= (isA u ty$int) (= (ty u) ty$int)) :pattern ((isA u ty$int)))))
(assert (forall ((u universe)) (! (= (isA u ty$null) (= (ty u) ty$null)) :pattern ((isA u ty$null)))))
(assert (forall ((u universe) (t type)) (! (= (isA u (ty$set t)) (= (ty u) (ty$set t))) :pattern ((isA u (ty$set t))) )))
(assert (forall ((u universe) (t type)) (! (= (isA u (ty$array t)) (or (= (ty u) (ty$array t)) (= (ty u) ty$null))) :pattern ((isA u (ty$array t))))))
(assert (forall ((u universe) (t type)) (! (= (isA u (ty$array2 t)) (or (= (ty u) (ty$array2 t)) (= (ty u) ty$null))) :pattern ((isA u (ty$array2 t))) )))
<classes:{ n | (assert (forall ((u universe)) (! (= (isA u class$<n>) (or (= (ty u) class$<n>) (= (ty u) ty$null))) :pattern ((isA u class$<n>)) )))
}>

; == Embedding into universe
(declare-fun u2i (universe) Int)
(declare-fun i2u (Int) universe)
(assert (forall ((i Int)) (! (= (u2i (i2u i)) i) :pattern ((u2i (i2u i))))))
(assert (forall ((i Int)) (= (ty (i2u i)) ty$int)))
(assert (forall ((u universe)) (=> (= (ty u) ty$int) (= (i2u (u2i u)) u))))

(declare-fun u2b (universe) Bool)
(declare-fun b2u (Bool) universe)
(assert (forall ((b Bool)) (= (u2b (b2u b)) b)))
(assert (forall ((b Bool)) (= (ty (b2u b)) ty$bool)))
(assert (forall ((u universe)) (=> (= (ty u) ty$bool) (= (b2u (u2b u)) u))))

(declare-fun u2h (universe) Heap)
(declare-fun h2u (Heap) universe)
(assert (forall ((h Heap)) (= (u2h (h2u h)) h)))
(assert (forall ((h Heap)) (= (ty (h2u h)) ty$heap)))
(assert (forall ((u universe)) (=> (= (ty u) ty$heap) (= (h2u (u2h u)) u))))

(declare-fun coerce (universe type) universe)
(assert (forall ((u universe)(t type))
  (! (isA (coerce u t) t) :pattern ((coerce u t)))))
(assert (forall ((u universe)(t type))
  (! (=> (isA u t) (= (coerce u t) u)) :pattern ((coerce u t)) )))

; === Sets

(declare-fun $in (universe universe) Bool)

; === Heap operations

(declare-fun $len0 (universe) Int)
(assert (forall ((u universe)) (! (>= ($len0 u) 0) :pattern (($len0 u)) )))

(declare-const $heap universe)
(assert (= (ty $heap) ty$heap))

(declare-const null universe)
(assert (= (ty null) ty$null))
(assert (forall ((u universe)) (=> (= (ty u) ty$null) (= u null))))

(declare-fun $anon (Heap universe Heap) Heap)
(assert (forall ((h Heap)(m universe)(h2 Heap)(o universe)(f field))
 (! (= (select ($anon h m h2) o f)
       (select (ite ($in o m) h2 h) o f)) :pattern ((select ($anon h m h2) o f)) )))

; --- Fields
(declare-fun fieldSerialNo (field) Int)

(declare-fun arrIdx (Int) field)
(assert (forall ((i Int)) (! (=> (>= i 0) (= (fieldSerialNo (arrIdx i)) i)) :pattern ((arrIdx i)) )))

<fields:{ f |
(declare-const |field$<f>| field)
(assert (= (fieldSerialNo |field$<f>|) -<i>))

}>

; === Builtin functions

(declare-const $everything universe)
(assert (forall ((u universe)) 
                (! (= ($in u $everything) (isA u ty$object)) :pattern (($in u $everything)) )))


<!
;; select<C, D>  (heap, C, field<C,D>) --> D
;; select<C,D>(h, r, f)  -->
;;   (o2c$D (u2o (select h (c2o$C r) f)))
;; store<C, D> (heap, C, field<C,D>, D) --> heap
;;   (store heap (c2o$C r) f (o2u (c2o$D value)))
!>