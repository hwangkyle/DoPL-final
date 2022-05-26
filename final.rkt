#lang racket
(require redex)

(define-language transient-λ
  (n ::= number)
  (x f ::= variable-not-otherwise-mentioned)
  
  ;--- FIGURE 2 ---
  (es ::= x (fun f (x T) (es T)) (es es) (ref es) (! es) (:= es es) n (+ es es))
  (Γ ::= ((x T) ...))
  (T ::= int (T -> T) dyn (ref T))
  (e ::= (error x S) x v (fun f x e) (e e) (+ e e) (! e) (:= e e) (=> e T T) (d=> e (S e)))
  (S ::= int -> ref dyn)
  (a ::= number)
  
  ;--- FIGURE 4 ---
  (E ::= hole (E e) (v E) (+ E e) (+ v E) (ref E) (! E) (:= E e) (=> E T T) (d=> E (S e)) (d=> v S E))
  (γ ::= (e σ))
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
                           (+ 1 (apply max (term (a ...))))
                           0)])

;-----------
; FUNCTIONS
;-----------

;--- FIGURE 3 ---

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
   (|| T_1 S)
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
        (a ((a (λ (x) e)) (a_1 h_1) ...))
        (where a (fresh-σ ((a_1 h_1) ...)))
        λ1]

   [--> ((a v) σ)
        (?)
        (side-condition (redex-match? transient-λ (λ (x) e) (term (find-σ a σ))))
        λ2]

   
   [--> ((+ n_1 n_2) σ)
        (,(+ (term n_1) (term n_2)) σ)
        λ3]


   [--> ((=> v T_1 T_2) σ)
        (v σ)
        (judgment-holds (|| v S))
        (judgment-holds (hastype σ v S))
        λ4]

   [--> ((=> v T_1 T_2) σ)
        error ; add this somewhere
        λ5]


   [--> ((d=> v (S a)) σ)
        (v σ)
        (judgment-holds (|| v S))
        (judgment-holds (hastype σ v S))
        λ6]

   [--> ((d=> v (S a)) σ)
        error ; again
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

(test-judgment-holds (hastype () 1 int))
(test-judgment-holds (hastype ((0 1) (1 (λ (asdf) 3))) 1 int))
(test-judgment-holds (hastype () 1 dyn))
(test-judgment-holds (hastype ((0 1) (1 (λ (asdf) 3))) 1 dyn))
; we have troubles below
(test-judgment-holds (hastype () 1 ->))
(test-judgment-holds (hastype ((0 1) (1 (λ (asdf) 3))) 1 ->))

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
 (term (0 ((0 (λ (x) 1))))
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