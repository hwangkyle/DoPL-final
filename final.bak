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
;  (a ::= (addr number))
#|
  (E ::= hole (E e) (v E) (+ E e) (+ v E) (ref E) (! E) (:= E e)) ; + some more
  (state ::= (e σ))
  (v ::= n a)
  (σ ::= (->> a h \sigma))
  (h ::= (λ (x) e) v)
  (L ::= intq ->q refq dyn)
  (q ::= ϵ)
|#)

(define-judgment-form transient-λ
  #:mode (~> I I O O)
  #:contract (~> es S e T)

  [
   ---
   (~> Γ n n int)]

  [
   ---
   (~> Γ x x (Γ x))]

  [(~> Γ es_1 e_1 int)
   (~> Γ es_2 e_2 int)
   ---
   (~> (+ es_1 es_2) (+ e e) int)]

 
  )

(define-judgment-form transient-λ
  #:mode (|| I I)
  #:contract (|| e e)

  [

   ]
  
)

(define-judgment-form transient-λ
  #:mode (> I O)
  #:contract (> e e)
  [
 
)

(define-judgment-form transient-λ
  #:mode (~ I O)
  #:contract (~ e e)

  )
   
(define-metafunction transient-λ
  delta : e -> e
  [(delta (+ e_1 e_2)) ,(+ (term e_1) (term e_2))])

   
(define-metafunction transient-λ
  type-check : e S ->
  [(type-check e S) idk])
   
  
(define-metafunction transient-λ
  Γ : es -> T
  [(Γ (fun x (x T_1) (es T_2))) (T_1 -> T_2)]
  [(Γ (ref es)) (ref (Γ es))]
  [(Γ n) int]
  [(Γ x) dyn] ;; maybe fix later
  )
#|
(+ 1 2) 3
(+ (1::int=>int) (2::int=>int)) 3 or (3::int=>int)
(+ (1 d=> int e) (2 d=> int e)) 
|#
; cast function
(define-metafunction transient-λ
  cast : e T -> e
  [(cast e T) (=> e )]
  )

(define-metafunction transient-λ
  translate : es -> e
  [(translate x)
   ((Γ x) x)]
  [(translate (+ es_1 es_2))
   (+ (cast es_1 int) (cast es_2 int))]
  
  )

; Section 4.2
(define -->
  (reduction-relation
   transient-λ

   ; (--> function) : heap address pointing to function

   ; (--> function-application) : find func from heap then β-reduction

   ; (--> cast-expressions) : ...
   )
  )