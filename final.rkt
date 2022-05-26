#lang racket
(require redex)

(define-language transient-λ
  (n ::= number)
  (x f ::= variable-not-otherwise-mentioned)
  
  ;--- FIGURE 2 ---
  (es ::= x (fun f (x T) (es T)) (es es) (ref es) (! es) (:= es es) n (+ es es))
  (Γ ::= ((x T) ...))
  (T ::= int (T -> T) dyn (ref T))
  (e ::= x v (fun f x e) (e e) (+ e e) (! e) (:= e e) (=> e T T) (d=> e (S e)))
  (S ::= int -> ref dyn)
  (a ::= (addr number))
  
  ;--- FIGURE 4 ---
  (E ::= hole (E e) (v E) (+ E e) (+ v E) (ref E) (! E) (:= E e) (=> E T T) (d=> E (S e)) (d=> v S E))
  (γ ::= (e σ) error)
  (v ::= n a)
  (σ ::= ((a h) ...))
  (h ::= (λ (x) e) v)
  #:binding-forms
  (λ (x) e #:refers-to x)
)
(default-language transient-λ)

;---------
; HELPERS
;---------
(define-metafunction transient-λ
  find-Γ : x Γ -> T
  [(find-Γ x ((x T) (x_1 T_1) ...)) T]
  [(find-Γ x ((x_1 T_1) (x_2 T_2) ...)) (find-Γ x ((x_2 T_2) ...))])

(define-metafunction transient-λ
  find-σ : a σ -> h
  [(find-σ a ((a h) (a_1 h_1) ...)) h]
  [(find-σ a ((a_1 h_1) (a_2 h_2) ...)) (find-σ a ((a_2 h_2) ...))])

(define-metafunction transient-λ
  Γ-to-vars : Γ -> (x ...)
  [(Γ-to-vars ((x T) ...)) (x ...)])

(define-metafunction transient-λ
  new-name : (x ...) -> x
  [(new-name (x ...))  ,(gensym (apply string-append (map symbol->string (term (x ...)))))])

(define-metafunction transient-λ
  σ-to-addrs : σ -> (a ...)
  [(σ-to-addrs ((a h) ...)) (a ...)])

(define-metafunction transient-λ
  new-addr : (a ...) -> a
  [(new-addr (a ...)) ,(if (< 0 (length (term (a ...))))
                           (term (addr (+ 1 (apply max (term (a ...))))))
                           (term (addr 0)))])

(define-metafunction transient-λ
  v-tag : v -> S
  [(v-tag n) int]
  [(v-tag a) dyn])

;-----------
; FUNCTIONS
;-----------

;--- FIGURE 3 ---

; Γ - es ~> e:T
(define-judgment-form transient-λ
  #:mode (~> I I O O)
  #:contract (~> Γ es e T)

  [
   ---
   (~> Γ n n int)]

  [
   ---
   (~> Γ x x (find-Γ x Γ))]

  [(~> Γ es_1 e_1 T_1) (~ T_1 int)
                       (~> Γ es_2 e_2 T_2) (~ T_2 int)
                       ---
                       (~> Γ (+ es_1 es_2) (+ (=> e_1 T_1 int) (=> e_2 T_2 int)) int)]

  [(~>
    ((f T_1 -> T_2) (x_1 T_1) (x T) ...)
    es
    e
    T_3)
   (where S (|| T_1))
   (~ T_2 T_3)
   ---
   (~> ((x T) ...)
       (fun f (x_1 T_1) (es T_2))
       (fun f x_1 (substitute e x_1 (d=> x_1 S)))
       int)]

  [(~> Γ es_1 e_1 T)
   (> T (T_1 -> T_2))
   (~> Γ es_2 e_2 T_3)
   (~ T_1 T_3)
   (where f (fresh-Γ Γ))
   (where S (|| T_2))
   ---
   (~> Γ
       (es_1 es_2)
       (substitute (d=> (f (=> e_2 T_3 T_1)) S f)
                   f
                   (=> e_1 T (T_1 -> T_2)))
       T_2)]
  )

(define-metafunction transient-λ
  || : T -> S
  [(|| dyn) dyn]
  [(|| int) int]
  [(|| (T_1 -> T_2)) ->]
  )

(define-judgment-form transient-λ
  #:mode (> I O)
  #:contract (> T T)

  [
   ---
   (> (T_1 -> T_2) (T_1 -> T_2))]

  [
   ---
   (> dyn (dyn -> dyn))]
  )

(define-judgment-form transient-λ
  #:mode (~ I I)
  #:contract (~ T T)
  [
   ---
   (~ int int)]

  [
   ---
   (~ dyn T)]

  [
   ---
   (~ T dyn)]

  [(~ T_1 T_3)
   (~ T_2 T_4)
   ---
   (~ (T_1 -> T_2) (T_3 -> T_4))]
  )

(define-metafunction transient-λ
  fresh-Γ : Γ -> x
  [(fresh-Γ Γ) (new-name (Γ-to-vars Γ))])

(define-metafunction transient-λ
  fresh-σ : σ -> a
  [(fresh-σ σ) (new-addr (σ-to-addrs σ))])


;--- FIGURE 4 ---

; <e, σ> --> γ
(define -->λ
  (reduction-relation
   transient-λ

   [--> ((fun f x e) ((a_1 h_1) ...))
        (a ((a (λ (x) (substitute e f a))) (a_1 h_1) ...))
        (where a (fresh-σ ((a_1 h_1) ...)))
        λ1]

   [--> ((a v) σ)
        ((substitute e x v) σ)
        (side-condition (redex-match? transient-λ (λ (x) e) (term (find-σ a σ))))
        (where (λ (x) e) (find-σ a σ))
        λ2]

   
   [--> ((+ n_1 n_2) σ)
        (,(+ (term n_1) (term n_2)) σ)
        λ3]


   [--> ((=> v T_1 T_2) σ)
        (v σ)
        (where S (|| T_2))
        (side-condition (judgment-holds (hastype σ v S)))
        λ4]

   [--> ((=> v T_1 T_2) σ)
        (error σ) ; σ not needed, i think, but kept just in case
        (where S (|| T_2))
        (side-condition (not (judgment-holds (hastype σ v S))))
        λ5]


   [--> ((d=> v (S a)) σ)
        (v σ)
        (side-condition (judgment-holds (hastype σ v S)))
        λ6]

   [--> ((d=> v (S a)) σ)
        (error σ)
        (side-condition (not (judgment-holds (hastype σ v S))))
        λ7]
   ))

; hastype(σ, v, S)
(define-judgment-form transient-λ
  #:mode (hastype I I I)
  #:contract (hastype σ v S)
  [
   ---
   (hastype σ n int)]

  [
   ---
   (hastype σ v dyn)]

  [(side-condition ,(redex-match? transient-λ (λ (x) e) (term (find-σ a σ))))
   ---
   (hastype σ a ->)]
  )

;-------
; TESTS
;-------
(test-equal (term (find-Γ asdf ((qwer dyn) (asdf int) (poiu (int -> int))))) (term int))
(test-equal (term (find-σ (addr 2) (((addr 1) 9) ((addr 2) 8) ((addr 3) 7)))) (term 8))

(test-judgment-holds (~> () 1 1 int))
(test-judgment-holds (~> ((asdf int) (fdsa dyn)) asdf asdf int))
; TODO: more tests

(test-equal (term (|| dyn)) (term dyn))
(test-equal (term (|| int)) (term int))
(test-equal (term (|| (int -> int))) (term ->))
(test-equal (term (|| ((int -> int) -> (dyn -> dyn)))) (term ->))

(test-judgment-holds (> dyn (dyn -> dyn)))
(test-judgment-holds (> (int -> int) (int -> int)))
(test-judgment-holds (> (int -> (int -> dyn)) (int -> (int -> dyn))))

(test-judgment-holds (~ int int))
(test-judgment-holds (~ dyn int))
(test-judgment-holds (~ dyn dyn))
(test-judgment-holds (~ dyn (int -> dyn)))
(test-judgment-holds (~ int dyn))
(test-judgment-holds (~ (int -> dyn) dyn))
(test-judgment-holds (~ (int -> dyn) (int -> dyn)))
(test-judgment-holds (~ (int -> dyn) (dyn -> dyn)))
(test-judgment-holds (~ (dyn -> dyn) ((int -> dyn) -> (int -> ((dyn -> int) -> (int -> int))))))

(test-judgment-holds (hastype () 1 int))
(test-judgment-holds (hastype (((addr 0) 1) ((addr 1) (λ (asdf) 3))) 1 int))
(test-judgment-holds (hastype () 1 dyn))
(test-judgment-holds (hastype (((addr 0) 1) ((addr 1) (λ (asdf) 3))) 1 dyn))
; (test-judgment-holds (hastype () (addr 1) ->))
(test-judgment-holds (hastype (((addr 0) 1) ((addr 1) (λ (asdf) 3))) (addr 1) ->))

; lazy coding: assumes p is a valid program e
(define (load-lang p)
  (term (,p ())))

(test-equal
 (term
  ,(first
    (apply-reduction-relation*
     -->λ
     (load-lang
      (term (fun f x 1))
      ))))
 (term ((addr 0) (((addr 0) (λ (x) 1))))
       ))

(test-equal
 (first
  (term
   ,(first
     (apply-reduction-relation*
      -->λ
      (load-lang
       (term (+ 1 2))
       )))))
 (term 3))

(test-equal
 (first
  (term
   ,(first
     (apply-reduction-relation*
      -->λ
      (load-lang
       (term (=> 1 int int))
       )))))
 (term 1))

(test-equal
 (first
  (term
   ,(first
     (apply-reduction-relation*
      -->λ
      (load-lang
       (term (=> 1 int dyn))
       )))))
 (term 1))

(test-equal
 (first
  (term
   ,(first
     (apply-reduction-relation*
      -->λ
      (load-lang
       (term (=> 1 int (int -> int)))
       )))))
 (term error))

(test-equal
 (first
  (term
   ,(first
     (apply-reduction-relation*
      -->λ
      (load-lang
       (term (d=> 1 (int (addr 0))))
       )))))
 (term 1))

(test-equal
 (first
  (term
   ,(first
     (apply-reduction-relation*
      -->λ
      (load-lang
       (term (d=> 1 (dyn (addr 0))))
       )))))
 (term 1))

(test-equal
 (first
  (term
   ,(first
     (apply-reduction-relation*
      -->λ
      (load-lang
       (term (d=> 1 (-> (addr 0))))
       )))))
 (term error))