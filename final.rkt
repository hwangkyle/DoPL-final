#lang racket
(require redex)

(define-language transient-λ
  (n ::= number)
  (x ::= variable-not-otherwise-mentioned)
  
  (es ::= x (fun x (x T) (es T)) (es es) (ref es) (! es) (:= es es) n (+ es es))
  (Γ ::= ((x T) ...))
  (T ::= int (T -> T) dyn (ref T))
  (e ::= (error x S) x v (fun x x e) (e e) (+ e e) (! e) (:= e e) (=> e T T) (d=> e (S e)))
  (S ::= int -> ref dyn)
  (a ::= number)
  
  (E ::= hole (E e) (v E) (+ E e) (+ v E) (ref E) (! E) (:= E e) (=> E T T) (d=> E (S e)) (d=> v S E))
  (γ ::= (e σ))
  (v ::= n a)
  (σ ::= ((a h) ...))
  (h ::= (λ (x) e) v)
)
(default-language transient-λ)

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
    ((x_1 T_1 -> T_2) (x_2 T_1) (x T) ...)
    es
    e
    T_3)
   (|| T_1 S)
   (~ T_2 T_3)
   ---
   (~> ((x T) ...)
       (fun x_1 (x_2 T_1) (es T_2))
       (fun x_1 x_2 (substitute e x_2 (d=> x_2 S)))
       int)]

  [(~> Γ es_1 e_1 T)
   (> T (T_1 -> T_2))
   (~> Γ es_2 e_2 T_3)
   (~ T_1 T_3)
   (where f (fresh Γ))
   (|| T_2 S)
   ---
   (~> Γ
       (es_1 es_2)
       (substitute (d=> (f (=> e_2 T_3 T_1)) S f)
                   f
                   (=> e_1 T (T_1 -> T_2)))
       T_2)]
  )

(define-judgment-form transient-λ
  #:mode (|| I O)
  #:contract (|| T S)

  [
   ---
   (|| dyn dyn)]

  [
   ---
   (|| int int)]

  [
   ---
   (|| (T_1 -> T_2) ->)]
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
  Γ-to-vars : Γ -> (x ...)
  [(Γ-to-vars ((x T) ...)) (x ...)])

(define-metafunction transient-λ
  new-name : (x ...) -> x
  [(new-name (x ...)) (term ,(gensym (string-append apply (map symbol->string (term (x ...))))))])

(define-metafunction transient-λ
  σ-to-addrs : σ -> (a ...)
  [(σ-to-addrs ((a h) ...)) (a ...)])

(define-metafunction transient-λ
  new-addr : (a ...) -> a
  [(new-addr (a ...)) ,(max ,(flatten (term (a ...))))])

; make new fresh function
(define-metafunction transient-λ
  fresh : Γ or σ -> x or a
  [(fresh Γ) (new-name (Γ-to-vars Γ))]
  [(fresh σ) (new-addr (σ-to-addrs σ))])

(define -->
  (reduction-relation
   transient-λ

   [--> ((fun x_1 x_2 e) ((a_1 h_1) ...)
        (a ((a (λ (x) e)) (a_1 h_1) ...))
        (side-condition 

(define-judgment-form transient-λ
  #:mode (hastype I I I)
  #:contract (hastype σ v S)
  [
   ---
   (hastype σ n int)]

  [
   ---
   (hastype σ v dyn)]

  [(redex-match? transient-λ (λ (x) e) (find-σ a σ))
   ---
   (hastype σ a ->)]
  )

; ---------
; HELPERS
; ---------
(define-metafunction transient-λ
  find-Γ : x Γ -> T
  [(find-Γ x ((x T) (x_1 T_1) ...)) T]
  [(find-Γ x ((x_1 T_1) (x_2 T_2) ...)) (find-Γ x ((x_2 T_2) ...))])

(define-metafunction transient-λ
  find-σ : a σ -> h
  [(find-σ a ((a h) (a_1 h_1) ...)) h]
  [(find-σ a ((a_1 h_1) (a_2 h_2) ...)) (find-σ a ((a_2 h_2) ...))])

; ---------
; TESTS
; ---------
(test-equal (term (find-Γ asdf ((qwer dyn) (asdf int) (poiu (int -> int))))) (term int))
(test-equal (term (find-σ 2 ((1 9) (2 8) (3 7)))) (term 8))

(test-judgment-holds (~> () 1 1 int))
(test-judgment-holds (~> ((asdf int) (fdsa dyn)) asdf asdf int))
; TODO: more tests

(test-judgment-holds (|| dyn dyn))
(test-judgment-holds (|| int int))
(test-judgment-holds (|| (int -> int) ->))
(test-judgment-holds (|| ((int -> int) -> (dyn -> dyn)) ->))

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