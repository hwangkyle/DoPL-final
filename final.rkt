#lang racket
(require redex)

; INTRO: Kyle

(define-language transient-λ
  (n ::= number)
  (x f ::= variable-not-otherwise-mentioned)

  ; David
  ;--- FIGURE 2 ---
  (es ::= x (fun f (x T) (es T)) (es es) (ref es) (! es) (:= es es) n (+ es es))
  (Γ ::= ((x T) ...))
  (T ::= int (T -> T) dyn (ref T))
  (e ::= error x v (fun f x e) (e e) (+ e e) (! e) (:= e e) (=> e T T) (d=> e S))
  (S ::= int -> ref dyn)
  (a ::= (addr number))

  ; Cindy
  ;--- FIGURE 4 ---
  (E ::= hole (E e) (v E) (+ E e) (+ v E) (ref E) (! E) (:= E e) (=> E T T) (d=> E S)) ;(d=> v S))
  (γ ::= (e σ))
  (v ::= n a)
  (σ ::= ((a h) ...))
  (h ::= (λ (x) e) v)
  #:binding-forms
  (λ (x) e #:refers-to x)
)
(default-language transient-λ)

; Kyle
;---------
; HELPERS
;---------
; searches through Γ and returns the type T of x.
; assumes x is in Γ
(define-metafunction transient-λ
  find-Γ : x Γ -> T
  [(find-Γ x ((x T) (x_1 T_1) ...)) T]
  [(find-Γ x ((x_1 T_1) (x_2 T_2) ...)) (find-Γ x ((x_2 T_2) ...))])

; searches through σ and returns h associated with address a.
; assumes a is in σ
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
                           (term (addr ,(+ 1 (apply max (map second (term (a ...)))))))
                           (term (addr 0)))])

;-----------
; FUNCTIONS
;-----------

(define-metafunction transient-λ
  fresh-Γ : Γ -> x
  [(fresh-Γ Γ) (new-name (Γ-to-vars Γ))])

(define-metafunction transient-λ
  fresh-σ : σ -> a
  [(fresh-σ σ) (new-addr (σ-to-addrs σ))])

; David
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

  [(~> Γ es_1 e_1 T_1)
   (~ T_1 int)
   (~> Γ es_2 e_2 T_2)
   (~ T_2 int)
   ---
   (~> Γ (+ es_1 es_2) (+ (=> e_1 T_1 int) (=> e_2 T_2 int)) int)]

  ; T_3 = T'_2
  ; e   = e'
  [(~>
    ((f (T_1 -> T_2)) (x_1 T_1) (x T) ...)
    es
    e
    T_3)
   (where S (|| T_1))
   (~ T_2 T_3)
   ---
   (~> ((x T) ...)
       (fun f (x_1 T_1) (es T_2))
       (fun f x_1 (substitute e x_1 (d=> x_1 S)))
       (T_1 -> T_2))]

  ; T_3 = T'_1
  [(~> Γ es_1 e_1 T)
   (> T (T_1 -> T_2))
   (~> Γ es_2 e_2 T_3)
   (~ T_1 T_3)
   (where f (fresh-Γ Γ))
   (where S (|| T_2))
   ---
   (~> Γ
       (es_1 es_2)
       (substitute (d=> (f (=> e_2 T_3 T_1)) S)
                   f
                   (=> e_1 T (T_1 -> T_2)))
       T_2)]
  )

; |T| = S
(define-metafunction transient-λ
  || : T -> S
  [(|| dyn) dyn]
  [(|| int) int]
  [(|| (T_1 -> T_2)) ->]
  )

; T |> T
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

; T ~ T
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


; Cindy
;--- FIGURE 4 ---

; <e, σ> --> γ
(define -->λ
  (reduction-relation
   transient-λ

   [--> ((in-hole E (fun f x e)) ((a_1 h_1) ...))
        ((in-hole E a) ((a (λ (x) (substitute e f a))) (a_1 h_1) ...))
        (where a (fresh-σ ((a_1 h_1) ...)))
        fun]

   [--> ((in-hole E (a v)) σ)
        ((in-hole E (substitute e x v)) σ)
        (side-condition (redex-match? transient-λ (λ (x) e) (term (find-σ a σ))))
        (where (λ (x) e) (find-σ a σ))
        app]

   
   [--> ((in-hole E (+ n_1 n_2)) σ)
        ((in-hole E ,(+ (term n_1) (term n_2))) σ)
        add]


   [--> ((in-hole E (=> v T_1 T_2)) σ)
        ((in-hole E v) σ)
        (where S (|| T_2))
        (side-condition (judgment-holds (hastype σ v S)))
        =>val]

   [--> ((in-hole E (=> v T_1 T_2)) σ)
        (error ())
        (where S (|| T_2))
        (side-condition (not (judgment-holds (hastype σ v S))))
        =>err]


   [--> ((in-hole E (d=> v S)) σ)
        ((in-hole E v) σ)
        (side-condition (judgment-holds (hastype σ v S)))
        d=>val]

   [--> ((in-hole E (d=> v S)) σ)
        (error ())
        (side-condition (not (judgment-holds (hastype σ v S))))
        d=>err]
   ))

; hastype(σ, v, S)
(define-judgment-form transient-λ
  #:mode (hastype I I I)
  #:contract (hastype σ v S)
  [
   ---
   (hastype σ n int)]

  [(side-condition ,(redex-match? transient-λ (λ (x) e) (term (find-σ a σ))))
   ---
   (hastype σ a ->)]

  [
   ---
   (hastype σ v dyn)]
  )

; Kyle
;-------
; TESTS
;-------
(test-equal (term (find-Γ asdf ((qwer dyn) (asdf int) (poiu (int -> int))))) (term int))
(test-equal (term (find-σ (addr 2) (((addr 1) 9) ((addr 2) 8) ((addr 3) 7)))) (term 8))

(test-judgment-holds (~> () 1 1 int))
(test-judgment-holds (~> ((asdf int) (fdsa dyn)) asdf asdf int))
(test-judgment-holds (~> () (+ 2 3) (+ (=> 2 int int) (=> 3 int int)) int))

; shows different casting
(test-judgment-holds (~> ((x int)) (+ 1 x) (+ (=> 1 int int) (=> x int int)) int))
(test-judgment-holds (~> ((x dyn)) (+ 1 x) (+ (=> 1 int int) (=> x dyn int)) int))

; shows same function, different types
(test-judgment-holds
 (~> ()
     (fun add1 (x int) ((+ 1 x) int))
     (fun add1 x (+ (=> 1 int int) (=> (d=> x int) int int)))
     (int -> int)))
(test-judgment-holds
 (~> ()
     (fun add1 (x dyn) ((+ 1 x) dyn))
     (fun add1 x (+ (=> 1 int int) (=> (d=> x dyn) dyn int)))
     (dyn -> dyn)))

; function call
(test-judgment-holds
 (~> ()
     ((fun add1 (x int) ((+ 1 x) int))
      1)
     (d=> ((=> (fun add1 x (+ (=> 1 int int) (=> (d=> x int) int int)))
               (int -> int)
               (int -> int))
           (=> 1 int int))
          int)
     int))
(test-judgment-holds
 (~> ()
     ((fun add1 (x dyn) ((+ 1 x) dyn))
      1)
     (d=> ((=> (fun add1 x (+ (=> 1 int int) (=> (d=> x dyn) dyn int)))
               (dyn -> dyn)
               (dyn -> dyn))
           (=> 1 int dyn))
          dyn)
     dyn))

; though this is translatable and passes through ~>, it can be seen that this is not evaluatable.
(test-judgment-holds
 (~> ()
     ((fun add1 (x dyn) ((+ 1 x) dyn))
      (fun add1 (x dyn) ((+ 1 x) dyn)))
     (d=> ((=> (fun add1 x (+ (=> 1 int int) (=> (d=> x dyn) dyn int)))
               (dyn -> dyn)
               (dyn -> dyn))
           (=> (fun add1 x (+ (=> 1 int int) (=> (d=> x dyn) dyn int)))
               (dyn -> dyn)
               dyn))
          dyn)
     dyn))

; more examples...
(test-judgment-holds
 (~> ()
     ((fun add1 (x int) ((+ 1 x) int))
      (+ 2 3))
     (d=> ((=> (fun add1 x (+ (=> 1 int int) (=> (d=> x int) int int)))
               (int -> int)
               (int -> int))
           (=> (+ (=> 2 int int) (=> 3 int int)) int int))
          int)
     int))
(test-judgment-holds
 (~> ()
     (fun f (g (int -> int)) ((g 1) int))
     (fun f g (d=> ((=> (d=> g ->) (int -> int) (int -> int))
                    (=> 1 int int))
                   int))
     ((int -> int) -> int)))
(test-judgment-holds
 (~> ()
     ((fun f (g (int -> int)) ((g 1) int))
      (fun add1 (x int) ((+ 1 x) int)))
     
     (d=> ((=> (fun f g (d=> ((=> (d=> g ->)
                                 (int -> int)
                                 (int -> int))
                             (=> 1 int int))
                            int))
               ((int -> int) -> int)
               ((int -> int) -> int))
           (=> (fun add1 x (+ (=> 1 int int) (=> (d=> x int) int int))) (int -> int) (int -> int)))
          int)
     int))

; a lot more complicated examples...
(test-judgment-holds
 (~> ()
     ((fun f (g (int -> int)) ((fun hh
                                    (ff ((int -> int) -> dyn))
                                    ((ff g) dyn))
                               (((int -> int) -> dyn) -> dyn)))
      (fun add1 (x int) ((+ 1 x) int)))
     
     (d=> ((=> (fun f g (fun hh ff (d=> ((=> (d=> ff ->)
                                             ((int -> int) -> dyn)
                                             ((int -> int) -> dyn))
                                         (=> (d=> g ->)
                                             (int -> int)
                                             (int -> int)))
                                        dyn)))
               ((int -> int) -> (((int -> int) -> dyn) -> dyn))
               ((int -> int) -> (((int -> int) -> dyn) -> dyn)))
           (=> (fun add1 x (+ (=> 1 int int) (=> (d=> x int) int int))) (int -> int) (int -> int)))
          ->)
     (((int -> int) -> dyn) -> dyn)))
(test-judgment-holds
 (~> ()
     (((fun f
            (g (int -> int))
            ((fun hh
                  (ff ((int -> int) -> dyn))
                  ((ff g) dyn))
             (((int -> int) -> dyn) -> dyn)))
       (fun add1 (x int) ((+ 1 x) int)))
      (fun f_1 (asdf (int -> dyn)) ((asdf 2) dyn)))
     
     (d=>
      ((=>
        (d=>
         ((=>
           (fun f g
                (fun hh ff
                     (d=>
                      ((=>
                        (d=> ff ->)
                        ((int -> int) -> dyn)
                        ((int -> int) -> dyn))
                       (=> (d=> g ->) (int -> int) (int -> int)))
                      dyn)))
           ((int -> int) -> (((int -> int) -> dyn) -> dyn))
           ((int -> int) -> (((int -> int) -> dyn) -> dyn)))
          (=> (fun add1 x (+ (=> 1 int int) (=> (d=> x int) int int))) (int -> int) (int -> int)))
         ->)
        (((int -> int) -> dyn) -> dyn)
        (((int -> int) -> dyn) -> dyn))
       (=>
        (fun f_1 asdf
             (d=>
              ((=>
                (d=> asdf ->)
                (int -> dyn)
                (int -> dyn))
               (=> 2 int int))
              dyn))
        ((int -> dyn) -> dyn)
        ((int -> int) -> dyn)))
      dyn)

     dyn))

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
 (term ((addr 0) (((addr 0) (λ (x) 1))))))

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
       (term (d=> 1 int))
       )))))
 (term 1))

(test-equal
 (first
  (term
   ,(first
     (apply-reduction-relation*
      -->λ
      (load-lang
       (term (d=> 1 dyn))
       )))))
 (term 1))

(test-equal
 (first
  (term
   ,(first
     (apply-reduction-relation*
      -->λ
      (load-lang
       (term (d=> 1 ->))
       )))))
 (term error))

(test-equal
 (first
  (term
   ,(first
     (apply-reduction-relation*
      -->λ
      (load-lang
       (term (+ (=> 1 int int) (=> 2 int int)))
       )))))
 (term 3))

(test-equal
 (first
  (term
   ,(first
     (apply-reduction-relation*
      -->λ
      (load-lang
       (term (+ (+ 2 3) (+ 1 3)))
       )))))
 (term 9))

(test-equal
 (first
  (term
   ,(first
     (apply-reduction-relation*
      -->λ
      (load-lang
       (term ((fun f x (+ x 1)) 3))
       )))))
 (term 4))

(test-equal
 (first
  (term
   ,(first
     (apply-reduction-relation*
      -->λ
      (load-lang
       (term (d=> ((=> (fun add1 x (+ (=> 1 int int) (=> (d=> x int) int int)))
                       (int -> int)
                       (int -> int))
                   (=> 1 int int))
                  int))
       )))))
 (term 2))
#;(traces -->λ (load-lang (term (d=> ((=> (fun add1 x (+ (=> 1 int int) (=> (d=> x int) int int)))
                                        (int -> int)
                                        (int -> int))
                                    (=> 1 int int))
                                   int))))

(test-equal
 (first
  (term
   ,(first
     (apply-reduction-relation*
      -->λ
      (load-lang
       (term (d=> ((=> (fun add1 x (+ (=> 1 int (int -> int)) (=> (d=> x int) int int)))
                       (int -> int)
                       (int -> int))
                   (=> 1 int int))
                  int))
       )))))
 (term error))
#;(traces -->λ (load-lang
       (term (d=> ((=> (fun add1 x (+ (=> 1 int (int -> int)) (=> (d=> x int) int int)))
                       (int -> int)
                       (int -> int))
                   (=> 1 int int))
                  int))
       ))
(test-equal
 (first
  (term
   ,(first
     (apply-reduction-relation*
      -->λ
      (load-lang
       (term (d=> ((=> (fun add1 x (+ (=> 1 int int) (=> (d=> x ->) int int)))
                       (int -> int)
                       (int -> int))
                   (=> 1 int int))
                  int))
       )))))
 (term error))
#;(traces -->λ (load-lang
       (term (d=> ((=> (fun add1 x (+ (=> 1 int int) (=> (d=> x ->) int int)))
                       (int -> int)
                       (int -> int))
                   (=> 1 int int))
                  int))
       ))

#;(traces -->λ (load-lang
       (term (d=> ((=> (fun add1 x (+ (=> (fun asdf fdsa (+ 1 1)) int int) (=> (d=> x int) int int)))
                       (int -> int)
                       (int -> int))
                   (=> 1 int int))
                  int))
       ))
#;(traces -->λ (load-lang
              (term
               ((fun f x (x 1))
                (fun g x (+ 1 x))))))