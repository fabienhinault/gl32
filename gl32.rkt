#lang racket

; https://personal.math.vt.edu/brown/doc/PSL(2,7)_GL(3,2).pdf

(require math/number-theory)
(require math/matrix)
(require math/array)
(require rackunit)

(define-syntax-rule (let1 a b body ...)
  (let ((a b)) body ...))

(define (no? l)
  (equal? l '()))

; map for objects
(define (mapo symbol l . arglists)
  (apply map (list* (λ (_ . args) (apply _ (cons symbol args)))
                    l arglists)))

(define (filtero predicate-symbol l)
  (filter (λ (_) (_ predicate-symbol)) l))

(define (mod2 n)
  (modulo n 2))

(define (mod7 n)
  (modulo n 7))

(define (length< l1 l2)
  (< (length l1) (length l2)))

(define (vector->list-not-0 v)
  (vector->list (vector-filter (λ (_) (not (equal? 0 _))) v)))

(define (cartesian-power n lst)
  (apply cartesian-product (build-list n (λ (_) lst))))

(check-equal? (cartesian-power 1 (range 3)) '((0) (1) (2)))
(check-equal? (cartesian-power 2 (range 3)) '((0 0) (0 1) (0 2) (1 0) (1 1) (1 2) (2 0) (2 1) (2 2)))

; get a list containing the binary writing of a number n
; n the number
; the size of the desired list
; result
(define (n->bit-list n size result)
  (if (equal? size 0)
      result
      (n->bit-list (arithmetic-shift n -1) (- size 1) (cons (bitwise-bit-field n 0 1) result)))) 

(check-equal? (n->bit-list 0 9 '())   '(0 0 0  0 0 0  0 0 0))
(check-equal? (n->bit-list 1 9 '())   '(0 0 0  0 0 0  0 0 1))
(check-equal? (n->bit-list 511 9 '()) '(1 1 1  1 1 1  1 1 1))

(define (bit-list->n list len result)
  (if (no? list)
      result
      (bit-list->n (cdr list) (- len 1) (+ (* 2 result) (car list)))))

(check-equal? (bit-list->n '(0 0 0  0 0 0  0 0 0) 9 0) 0)
(check-equal? (bit-list->n '(0 0 0  0 0 0  0 0 1) 9 0) 1)
(check-equal? (bit-list->n '(1 1 1  1 1 1  1 1 1) 9 0) 511)

(define (group-by-n l group-size result)
  (if (no? l)
      (reverse result)
      (group-by-n (list-tail l group-size) group-size
                  (cons (take l group-size) result))))

(check-equal? (group-by-n '(1 2 3 4 5 6 7 8 9) 3 '()) '((1 2 3) (4 5 6) (7 8 9)))

(define (n->matrix-list n)
  (group-by-n (n->bit-list n 9 '()) 3 '()))


(define (matrix->TeX mat)
  ( ~a "\\pmatrix{"
       (apply ~a
              (map
               (lambda (l3)
                 (~a (apply ~a l3 #:separator " & ") " \\cr "))
               (matrix->list* mat)))
       "}"))

;#######  #####
;#       #     #
;#       #     #
;#####    #####
;#       #     #
;#       #     #
;#        #####

;F8
(define (vector3+ . vector3s)
  (apply vector-map + vector3s))
(check-equal? (vector3+ #[1 1 1] #[1 1 0] #[0 1 0]) #[2 3 1])

(define (vector3+%2 . vector3s)
  (vector-map mod2 (apply vector3+ vector3s)))
  
;f8-vector->n is actually P(2) for polynomial P, but not modulo 2
(define (f8-vector->n v)
  (+ (vector-ref v 0) (* 2 (vector-ref v 1)) (* 4 (vector-ref v 2))))
(check-equal? (f8-vector->n #[0 0 0]) 0)
(check-equal? (f8-vector->n #[1 0 0]) 1)
(check-equal? (f8-vector->n #[0 1 0]) 2)
(check-equal? (f8-vector->n #[1 1 0]) 3)
(check-equal? (f8-vector->n #[0 0 1]) 4)
(check-equal? (f8-vector->n #[1 0 1]) 5)
(check-equal? (f8-vector->n #[0 1 1]) 6)
(check-equal? (f8-vector->n #[1 1 1]) 7)

(define (n->f8-vector n)
  (build-vector 3 (λ (_) (bitwise-bit-field n _ (+ _ 1)))))
(check-equal? #[0 0 0] (n->f8-vector 0))
(check-equal? #[1 0 0] (n->f8-vector 1))
(check-equal? #[0 1 0] (n->f8-vector 2))
(check-equal? #[1 1 0] (n->f8-vector 3))
(check-equal? #[0 0 1] (n->f8-vector 4))
(check-equal? #[1 0 1] (n->f8-vector 5))
(check-equal? #[0 1 1] (n->f8-vector 6))
(check-equal? #[1 1 1] (n->f8-vector 7))

(define f8-vectors (make-vector 8))
(define f8s '())
(define f8-objects '())
(define _f8-by-powers #[])
(define __f8-0 '())

(define (_f8-object vector symbol power)
  (let* ((get-f8-by-power (λ (k) (if (equal? k ∞)
                                     __f8-0
                                     (vector-ref _f8-by-powers (mod7 k)))))
         (f8-monomial* (λ (coeffs powers)
                         (if (member 0 coeffs)
                             __f8-0
                             (get-f8-by-power (apply + powers)))))
         (alist (list (cons 'vector (λ (this) vector))
                    (cons 'symbol (λ (this) symbol))
                    (cons 'power (λ (this) power))
                    (cons 'coeff (λ (this i-coeff) (vector-ref vector i-coeff)))
                    (cons 'coeff==0? (λ (this i-coeff) (equal? 0 (vector-ref vector i-coeff))))
                    (cons '==? (λ (this other) (equal? vector (other 'vector))))
                    (cons 'in-array (λ (this) (array-ref f8-objects vector)))
                    (cons '*scalar (λ (this scalar) (if (equal? 0 scalar) __f8-0 this)))
                    (cons '+ (λ (this . others)
                               (array-ref f8-objects
                                          (apply vector3+%2 (cons vector (mapo 'vector others))))))
                    (cons '* (λ f8os
                               (if (member __f8-0 f8os)
                                   __f8-0
                                   (let1 indices-lists
                                         (cartesian-power (length f8os) (range 3))
                                          (apply __f8-0
                                                 (cons
                                                  '+
                                                  (map (λ (indices)
                                                         (f8-monomial* (mapo 'coeff f8os indices) indices))
                                                       indices-lists)))))))
                    ))
         (this '())
         (that (λ (symbol . args) (apply (cdr (assoc symbol alist)) (cons this args)))))
    (set! this that)
    this))

(define (f8==? _1 _2)
  (equal? (_1 'vector) (_2 'vector)))

(define ∞ +inf.0)
(define inf +inf.0)

(set! f8-objects (array #[#[#[(_f8-object #[0 0 0] '0 ∞) (_f8-object #[0 0 1] 'X2 2)]
                            #[(_f8-object #[0 1 0] 'X 1) (_f8-object #[0 1 1] 'X2+X 4)]]
                          #[#[(_f8-object #[1 0 0] '1 0) (_f8-object #[1 0 1] 'X2+1 6)]
                            #[(_f8-object #[1 1 0] 'X+1 3) (_f8-object #[1 1 1] 'X2+X+1 5)]]]))

(set! __f8-0 (array-ref f8-objects #(0 0 0)))
(define __f8-1 (array-ref f8-objects #(1 0 0)))
(define __f8-X (array-ref f8-objects #(0 1 0)))
(define __f8-X2 (array-ref f8-objects #(0 0 1)))
(define __f8-X+1 (array-ref f8-objects #(1 1 0)))
(define __f8-X2+X (array-ref f8-objects #(0 1 1)))
(define __f8-X2+X+1 (array-ref f8-objects #(1 1 1)))
(define __f8-X2+1 (array-ref f8-objects #(1 0 1)))


(check-equal? (__f8-X2+1 'vector) #[1 0 1])
(define (check==? actual expected)
  (check-true (actual '==? expected)))
(check==? __f8-0 (_f8-object #[0 0 0] 0 ∞))
(check-true (__f8-X2+1 'coeff==0? 1))
(check-false (__f8-X2+1 'coeff==0? 0))
(check-false (__f8-X2+1 'coeff==0? 2))

;vector of f8 objects by powers
;                              X^0   X^1     X^2    X^3     X^4        X^5        X^6
(set! _f8-by-powers (vector __f8-1 __f8-X __f8-X2 __f8-X+1 __f8-X2+X __f8-X2+X+1 __f8-X2+1))
(define (_get-f8-by-power k)
  (if (equal? k ∞)
      __f8-0
      (vector-ref _f8-by-powers k)))

(check==? __f8-X2+X+1 (_get-f8-by-power 5))
(check==? __f8-0 (_get-f8-by-power ∞))


(check==? (__f8-0 '* __f8-0) __f8-0)
(check==? (__f8-0 '* __f8-X2+X+1) __f8-0)
(check==? (__f8-1 '* __f8-1) __f8-1)
(check==? (__f8-1 '* __f8-X2+X+1) __f8-X2+X+1)
(check==? (__f8-X '* __f8-1) __f8-X)
(check==? (__f8-X '* __f8-X) __f8-X2)
(check==? (__f8-X2 '* __f8-1) __f8-X2)
(check==? (__f8-X2 '* __f8-X) __f8-X+1)
(check==? (__f8-X '* __f8-X __f8-X) __f8-X+1)
; (X2+X+1)(X2+1) = X4+X2+X3+X+X2+1
;                = X2+X+X2+X+1+X+X2+1
;                = X2+X
(check==? (__f8-X2+X+1 '* __f8-X2+1) __f8-X2+X)

(check==? (__f8-0 '+ __f8-0) __f8-0)
(check==? (__f8-0 '+ __f8-1) __f8-1)
(check==? (__f8-X '+ __f8-0) __f8-X)
(check==? (__f8-X '+ __f8-1) __f8-X+1)
(check==? (__f8-0 '+ __f8-X __f8-X __f8-1 __f8-X2) __f8-X2+1)
(check==? (__f8-X2+X+1 '+ __f8-X2+1) __f8-X)



; #####  #        #####   #####
;#     # #       #     # #     #
;#       #             #       #
;#  #### #        #####   #####
;#     # #             # #
;#     # #       #     # #
; #####  #######  #####  #######
  
;GL32 matrices
(define (n->gl32-matrix n)
  (list->matrix 3 3 (n->bit-list n 9 '())))

(check-equal? (n->gl32-matrix 0)   (matrix [[0 0 0] [0 0 0] [0 0 0]]))
(check-equal? (n->gl32-matrix 1)   (matrix ((0 0 0) (0 0 0) (0 0 1))))
(check-equal? (n->gl32-matrix 2)   (matrix ((0 0 0) (0 0 0) (0 1 0))))
(check-equal? (n->gl32-matrix 8)   (matrix ((0 0 0) (0 0 1) (0 0 0))))
;84 = 64 + 16 + 4 = 2**6 + 2**4 + 2**2
(check-equal? (n->gl32-matrix 84)  (matrix ((0 0 1) (0 1 0) (1 0 0))))

(define (gl32-matrix->n m)
  (let1 l (matrix->list m)
        (bit-list->n l 9 0)))

(check-equal? (gl32-matrix->n (matrix [[0 0 0] [0 0 0] [0 0 0]])) 0)
(check-equal? (gl32-matrix->n (matrix [[0 0 0] [0 0 0] [0 0 1]])) 1)
(check-equal? (gl32-matrix->n (matrix [[0 0 0] [0 0 1] [0 0 0]])) 8)
(check-equal? (gl32-matrix->n (matrix [[0 0 0] [0 0 0] [0 1 0]])) 2)
(check-equal? (gl32-matrix->n (matrix [[0 0 1] [0 1 0] [1 0 0]])) 84)
(check-equal? (gl32-matrix->n (n->gl32-matrix 98)) 98)

(define (gl32-matrix* m1 m2)
  (matrix-map mod2 (matrix* m1 m2)))

(check-equal? (gl32-matrix* (n->gl32-matrix 1) (n->gl32-matrix 1)) (n->gl32-matrix 1))
;;;;;;;
; gl32 objects

; powers of a GL32 object
(define (__get-gl32-powers o result)
  (let1 next ((car result) '* o)
        (if (next 'identity?)
            (reverse result)
            (__get-gl32-powers o (cons next result)))))

(define (gl32-object n)
  (let* ((mat (n->gl32-matrix n))
         (al (list
              (cons 'n (λ (this) n))
              (cons 'matrix (λ (this) mat))
              (cons 'equal? (λ (this other) (equal? (other 'n) n)))
              (cons '==? (λ (this other) (equal? (other 'n) n)))
              (cons 'identity? (λ (this) (equal? n 273)))
              (cons '* (λ (this other) (gl32-object (gl32-matrix->n (gl32-matrix* mat (other 'matrix))))))
              (cons 'gl32? (λ (this) (odd? (matrix-determinant mat))))
              (cons 'powers (λ (this) (__get-gl32-powers this (list this))))
              (cons 'image (λ (this vector3) (matrix->vector (gl32-matrix* mat (vector->matrix 3 1 vector3)))))
              (cons '*vector3 (λ (this vector3)
                                (matrix->vector (gl32-matrix* mat (vector->matrix 3 1 vector3)))))
              (cons '*f8 (λ (this f8o)
                           (array-ref f8-objects (this '*vector3 (f8o 'vector)))))
              (cons 'TeX (λ (this) (matrix->TeX mat)))
              ))
         (this '())
         (that (λ (symbol . args) (apply (cdr (assoc symbol al)) (cons this args)))))
    (set! this that)
    this))

(define _gl32-identity (gl32-object 273))
(check-true (_gl32-identity 'identity?))
(check-true ((_gl32-identity '* _gl32-identity) 'identity?))

(define _84 (gl32-object 84))
(check-false (_84 'identity?))
(check-true ((_gl32-identity '* _84) 'equal? _84))
(check-true ((_84 '* _gl32-identity) 'equal? _84))
(check-equal? (mapo 'n (_84 'powers)) '(84))
(check-equal? (_84 '*vector3 #[1 0 0]) #[0 0 1])
(define _85 (gl32-object 85))
(define _86 (gl32-object 86))
(define _98 (gl32-object 98))
(define _140 (gl32-object 140))

; M_3(ZZ_2) the set of all square matrices of dimension 3 in ZZ_2
(define _m3z2 (map gl32-object (range 0 512)))
;list of GL32 objects
(define _gl32-objects (filtero 'gl32? _m3z2))

(check-equal? (length _gl32-objects) 168)

(check==? (_84 '*f8 __f8-0) __f8-0)
(check==? (_84 '*f8 __f8-1) __f8-X2)
(check==? (_84 '*f8 __f8-X) __f8-X)
(check==? (_84 '*f8 __f8-X+1) __f8-X2+X)
(check==? (_84 '*f8 __f8-X2) __f8-1)
(check==? (_84 '*f8 __f8-X2+1) __f8-X2+1)
(check==? (_84 '*f8 __f8-X2+X) __f8-X+1)
(check==? (_84 '*f8 __f8-X2+X+1) __f8-X2+X+1)

(check==? (_85 '*f8 __f8-0) __f8-0)
(check==? (_85 '*f8 __f8-1) __f8-X2)
(check==? (_85 '*f8 __f8-X) __f8-X)
(check==? (_85 '*f8 __f8-X+1) __f8-X2+X)
(check==? (_85 '*f8 __f8-X2) __f8-X2+1)
(check==? (_85 '*f8 __f8-X2+1) __f8-1)
(check==? (_85 '*f8 __f8-X2+X) __f8-X2+X+1)
(check==? (_85 '*f8 __f8-X2+X+1) __f8-X+1)

(define (_T-1 ogl32)
  (λ (f7bar-nb)
    ((ogl32 '*f8 (_get-f8-by-power f7bar-nb)) 'power)))

(define _T-1-98 (_T-1 _98))
(check-equal? (_T-1-98 0) 1)
(check-equal? (_T-1-98 1) 2)
(check-equal? (_T-1-98 2) 0)
(check-equal? (_T-1-98 3) 4)
(check-equal? (_T-1-98 4) 6)
(check-equal? (_T-1-98 5) 5)
(check-equal? (_T-1-98 6) 3)
(check-equal? (_T-1-98 inf) inf)

;#################
;
;######### #######
;# #       #    #
;# #           #
;# #####      #
;# #         #
;# #         #
;###         #

(define (+7bar k l)
  (if (or (equal? k ∞) (equal? l ∞))
      ∞
      (mod7 (+ k l))))

(define (*7bar k l)
  (cond ((or (and (equal? k ∞) (not (equal? 0 l))) (and (equal? l ∞) (not (equal? k 0)))) ∞)
        ((or (equal? k ∞) (equal? l ∞)) +nan.0)
        (else (mod7 (* k l)))))

(define (inv7bar k)
  (if (equal? k ∞)
      0
      (vector-ref #[+inf.0 1 4 5 2 3 6] k)))

(define (/7bar k l)
  (*7bar k (inv7bar l)))

(define r7 (range 7))
(define 7bar
  (let* ((_∞ '())
         (numbers #[])
         (inverses #[])
         (methods
          (list (cons '∞? (λ (k) (equal? k _∞)))
                (cons '0? (λ (k) (equal? k (vector-ref numbers 0))))
                (cons '+ (λ (k l) (if (or (k '∞?) (l '∞?))
                                      _∞
                                      (vector-ref numbers(mod7 (+ (k 'k) (l 'k)))))))
                (cons '* (λ (k l) (cond ((or (and (k '∞?)
                                                  (not (l '0?)))
                                             (and (l '∞?)
                                                  (not (k '0?))))
                                         _∞)
                                        ((or (k '∞?) (l '∞?)) ; => other factor is 0
                                         +nan.0)
                                        (else (vector-ref numbers (mod7 (* (k 'k) (l 'k))))))))
                (cons 'inv (λ (k) (if (k '∞?)
                                      (vector-ref numbers 0)
                                      (vector-ref inverses (k 'k)))))
                (cons '/ (λ (k l) (k '* (l 'inv))))
                ))
         (ctor (λ (k)
                 (let* ((this '())
                        (that (λ (method-sym . args)
                                (if (equal? method-sym 'k)
                                    k
                                    (apply (cdr (assoc method-sym methods)) (cons this args))))))
                   (set! this that)
                   this)))
         )
    (set! _∞ (ctor ∞))
    (set! numbers (vector-map ctor (list->vector r7)))
    (set! inverses (vector-map (λ (_) (vector-ref numbers _)) #[0 1 4 5 2 3 6]))
    (vector-set! inverses 0 _∞)
    (λ (number)
      (if (equal? number ∞)
          _∞
          (vector-ref numbers number)))))

(check-equal? ((7bar ∞) '+ (7bar 0)) (7bar ∞))
(check-equal? ((7bar ∞) '+ (7bar 6)) (7bar ∞))
(check-equal? ((7bar 0) '+ (7bar 0)) (7bar 0))
(check-equal? ((7bar 1) '+ (7bar 0)) (7bar 1))
(check-equal? ((7bar 1) '+ (7bar 6)) (7bar 0))

(check-equal? ((7bar 1) '* (7bar 6)) (7bar 6))
(check-equal? ((7bar 2) '* (7bar 6)) (7bar 5))
(check-equal? ((7bar 1) '* (7bar ∞)) (7bar ∞))
(check-equal? ((7bar 1) '* (7bar 0)) (7bar 0))


(check-equal? ((7bar 1) '/ (7bar 6)) (7bar 6))
(check-equal? ((7bar 2) '/ (7bar 6)) (7bar 5))
(check-equal? ((7bar 1) '/ (7bar 5)) (7bar 3))
(check-equal? ((7bar 2) '/ (7bar 5)) (7bar 6))
(check-equal? ((7bar 1) '/ (7bar ∞)) (7bar 0))
(check-equal? ((7bar 1) '/ (7bar 0)) (7bar ∞))

;######   #####  #        #####  #######
;#     # #     # #       #     # #    #
;#     # #       #             #     #
;######   #####  #        #####     #
;#             # #       #         #
;#       #     # #       #         #
;#        #####  ####### #######   #


(define m2z7 (map (λ (_)(list->matrix 2 2 _))
                  (cartesian-product r7 r7 r7 r7)))
(define psl27-matrices (filter
                        (λ (_) (and (equal? 1 (mod7 (matrix-determinant _)))
                                    (or (<= 1 (matrix-ref _ 0 0) 3)
                                        (and (equal? 0 (matrix-ref _ 0 0))
                                             (<= 1 (matrix-ref _ 0 1) 3)))))
                        m2z7))
(check-equal? (length psl27-matrices) 168)
(define _3663 (last psl27-matrices))

(define (sf2 psl27-matrix)
  (let* ((a (matrix-ref psl27-matrix 0 0))
         (b (matrix-ref psl27-matrix 0 1))
         (c (matrix-ref psl27-matrix 1 0))
         (d (matrix-ref psl27-matrix 1 1)))
    (λ (k)
      (if (equal? k ∞)
          (if (equal? c 0)
              ∞
              (/7bar a c))
          (/7bar (+7bar (*7bar a k) b)
                 (+7bar (*7bar c k) d))))))

(define sf2-3663 (sf2 _3663))
(check-equal? (sf2-3663 0) 2) ; 6/3 = -1*5 = -5 = 2
(check-equal? (sf2-3663 1) 1) ; (3 + 6)/(6 + 3) = 1
(check-equal? (sf2-3663 2) 5) ; (2*3 + 6)/(2*6 + 3) = -2/1 = 5
(check-equal? (sf2-3663 3) ∞) ; (3*3 + 6)/(3*6 + 3) = 1/0 = ∞
(check-equal? (sf2-3663 4) 3) ; (4*3 + 6)/(4*6 + 3) = -3/-1 = 3
(check-equal? (sf2-3663 5) 0) ; (5*3 + 6)/(5*6 + 3) = (15 - 1)/(-5 + 3) = 0
(check-equal? (sf2-3663 6) 6) ; (6*3 + 6)/(6*6 + 3) = (-3 - 1)/(1 + 3) = -1 = 6
(check-equal? (sf2-3663 ∞) 4) ; 3/6 = -3 = 4

(define (__sf2->glf8 sf2)
  (λ (f8o)
    (let1 k (f8o 'power)
          ((_get-f8-by-power (sf2 k)) '+ (_get-f8-by-power (sf2 ∞))))))

(define __glf8-3663 (__sf2->glf8 sf2-3663))

(check==? (__glf8-3663 __f8-1) __f8-X)          ; = X^f(0) + X^f(∞) = X^2 + X^4 = X^2 + X^2 + X          = X
(check==? (__glf8-3663 __f8-X) __f8-X2)         ; = X^f(1) + X^f(∞) = X + X^4   = X + X^2 + X            = X^2
(check==? (__glf8-3663 __f8-X2) __f8-1)         ; = X^f(2) + X^f(∞) = X^5 + X^4 = X^2 + X + 1 + X^2 + X  = 1
(check==? (__glf8-3663 __f8-X+1) __f8-X2+X)     ; = X^f(3) + X^f(∞) = X^∞ + X^4 = 0 + X^2 + X            = X^2 + X
(check==? (__glf8-3663 __f8-X2+X) __f8-X2+1)    ; = X^f(4) + X^f(∞) = X^3 + X^4 = X + 1 + X^2 + X        = X^2 + 1
(check==? (__glf8-3663 __f8-X2+X+1) __f8-X2+X+1); = X^f(5) + X^f(∞) = 1 + X^4   = 1 + X^2 + X            = X^2 + X + 1
(check==? (__glf8-3663 __f8-X2+1) __f8-X+1)     ; = X^f(6) + X^f(∞) = X^6 + X^4 = X^2 + 1 + X^2 + X      = X + 1
(check==? (__glf8-3663 __f8-0) __f8-0)          ; = X^f(∞) + X^f(∞)                                      = 0

(define (f->gl32-matrix f)
  (matrix-augment (map ->col-matrix (mapo 'vector  (map f (list __f8-1 __f8-X __f8-X2))))))

(define (sf2->gl32 sf2o)
  (gl32-object (gl32-matrix->n (f->gl32-matrix (__sf2->glf8 sf2o)))))

(check==? (sf2->gl32 sf2-3663) _98)

;list of cycles as lists of integers
;each element is:
;  - integer of the matrix
;  - length of the cycle (not counting identity)
;  - cycle (omitting identity)
;> powers
;'((84 1 (84))
;  (85 2 (85 340))
;  ...
;  (500 6 (500 335 229 187 426 94))
;  (501 3 (501 266 494)))
(define powers
  (map (λ (_)
         (let1 ns (mapo 'n (_ 'powers))
               (list (_ 'n) (length ns) ns )))
       _gl32-objects))


; vector of cycles as lists of integers
;> gl32-cycles-vector
;'#(0
;   ...
;   0
;   (84)
;   (85 340)
;   ...
;   (500 335 229 187 426 94)
;   (501 266 494)
;   0
;   ...
;   0)
(define gl32-cycles-vector (make-vector 512))
(for-each (λ (_) (vector-set! gl32-cycles-vector (car _) (caddr _)))
     powers)

; util function to build cycles-vector and lengths-vector
(define (add-cycle-element! cycle-element cycle-index cycle-length cycles-vector lengths-vector)
  (when (< (vector-ref lengths-vector cycle-element) cycle-length)
    (vector-set! cycles-vector cycle-element cycle-index)
    (vector-set! lengths-vector cycle-element cycle-length)))

; util function to build cycles-vector and lengths-vector
(define (add-cycle! cycle indices-vector lengths-vector)
  (map (λ (_)
         (add-cycle-element! _ (car cycle) (cadr cycle) indices-vector lengths-vector))
       (caddr cycle)))

; for each integer i corresponding to a matrix in GL(3,2), (vector-ref gl32-cycle-indices-vector i)
; will be the index of the first-found longest cycle
;> gl32-cycle-indices-vector
;'#(0
;   ...
;   0
;   254  ; at rank 84
;   ...
;   494  ; at rank 501
;   0
;   ...
;   0)
(define gl32-cycle-indices-vector (make-vector 512))

; for each integer i corresponding to a matrix in GL(3,2), (vector-ref gl32-lengths-vector i)
; will be the index of the first-found longest cycle
;> gl32-lengths-vector
;'#(0
;   ...
;   0
;   3  ; at rank 84
;   ...
;   3  ; at rank 501
;   0
;   ...
;   0)
(define gl32-lengths-vector (make-vector 512))

; build gl32-cycle-indices-vector gl32-lengths-vector
(for-each (λ (_) (add-cycle! _ gl32-cycle-indices-vector gl32-lengths-vector))
     powers)

; list of all 57 de-duplicated cycles
;> gl32-graph-cycles
;'((254 84 443)
;  ...
;  (395 474))
(define gl32-graph-cycles
  (map (λ (_) (vector-ref gl32-cycles-vector _))
       (remove-duplicates
        (vector->list
         (vector-filter (λ (_) (not (equal? 0 _))) gl32-cycle-indices-vector)))))

;;;;;;
; util fonctions for printing cycle graph

(define (move-left pred lst f-not-matching)
  (let-values (((matchings notmatchings) (partition pred lst)))
    (append matchings (f-not-matching notmatchings))))

(define (x-invariant? n)
  (equal? (arithmetic-shift n -6) 4))

(define (x-invariant-car? cycle-list)
  (x-invariant? (car cycle-list)))

(define (y-invariant? n)
  (equal? (modulo (arithmetic-shift n -3) 8) 2))

(define (y-invariant-car? cycle-list)
  (y-invariant? (car cycle-list)))

(define (z-invariant? n)
  (equal? (modulo n 8) 1))

(define (z-invariant-car? cycle-list)
  (z-invariant? (car cycle-list)))

(define gl32-graph-triangles
  (move-left x-invariant-car? (filter (λ (_) (equal? 2 (length _))) gl32-graph-cycles)
             (λ (_) (move-left y-invariant-car? _
                              (λ (_) (move-left z-invariant-car? _
                                                 (λ (_) _)))))))
             
(define gl32-graph-not-triangles
  (sort (filter-not (λ (_) (equal? 2 (length _))) gl32-graph-cycles)
        (λ (l1 l2) (< (length l1) (length l2)))))

(define (family-cycle->string cycle-list)
  (string-append "273 -- " (string-join (map ~a (map car cycle-list)) " -- ") ";"))

(define (family-triangle->string triangle-list)
  (string-append (string-join (map ~a (reverse (map car triangle-list))) " -- ") " -- 273;"))

(define (cycle->string cycle-list)
  (string-append "273 -- " (string-join (map ~a cycle-list) " -- ") ";"))

(define (triangle->string triangle-list)
  (string-append (string-join (map ~a (reverse triangle-list)) " -- ") " -- 273;"))


;(for-each displayln (map triangle->string gl32-graph-triangles))
;(for-each displayln (map cycle->string gl32-graph-not-triangles))

(define dot-struct-string-replacement-vector (vector " " "█"))

(define dot-html-string-replacement-vector (vector "" " BGCOLOR=\"black\""))

(define (row->dot-struct-string row)
  (string-append
   "{"
   (string-join (map (λ (_) (vector-ref dot-struct-string-replacement-vector _))
                     row)
                "|")
   "}"))

(check-equal? (row->dot-struct-string '(0 1 0)) "{ |█| }")

(define dot-square-length "18")
(define (row->dot-html-string row)
  (string-append
   "<tr>"
   (apply string-append
          (map (λ (coef)
                 (string-append
                  "<td HEIGHT=\""
                  dot-square-length
                  "\" WIDTH=\""
                  dot-square-length
                  "\""
                  (vector-ref dot-html-string-replacement-vector coef)
                  "></td>"))
                     row))
   "</tr>"))

(check-equal? (row->dot-html-string '(0 1 0))
              "<tr><td HEIGHT=\"18\" WIDTH=\"18\"></td><td HEIGHT=\"18\" WIDTH=\"18\" BGCOLOR=\"black\"></td><td HEIGHT=\"18\" WIDTH=\"18\"></td></tr>")

(define (matrix-list->dot-struct-string matrix-list)
  (string-join (map row->dot-struct-string matrix-list) "|"))

(define (matrix-list->dot-html-string matrix-list)
  (apply string-append (map row->dot-html-string matrix-list)))

(define (n->dot-struct-string n)
  (string-append
   (~a n)
   " [label=\""
   (matrix-list->dot-struct-string (n->matrix-list n))
   "\"];"))

(check-equal? (n->dot-struct-string 98) "98 [label=\"{ | |█}|{█| | }|{ |█| }\"];")

(define (n->dot-html-string n)
  (string-append
   (~a n)
   " [label=<<table BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\">"
   (matrix-list->dot-html-string (n->matrix-list n))
   "</table>>];"))

(check-equal? (n->dot-html-string 98)
              (string-append
               "98 [label=<<table BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\">"
               "<tr><td HEIGHT=\"18\" WIDTH=\"18\"></td><td HEIGHT=\"18\" WIDTH=\"18\"></td><td HEIGHT=\"18\" WIDTH=\"18\" BGCOLOR=\"black\"></td></tr>"
               "<tr><td HEIGHT=\"18\" WIDTH=\"18\" BGCOLOR=\"black\"></td><td HEIGHT=\"18\" WIDTH=\"18\"></td><td HEIGHT=\"18\" WIDTH=\"18\"></td></tr>"
               "<tr><td HEIGHT=\"18\" WIDTH=\"18\"></td><td HEIGHT=\"18\" WIDTH=\"18\" BGCOLOR=\"black\"></td><td HEIGHT=\"18\" WIDTH=\"18\"></td></tr></table>>];"
               ))

;(for-each displayln (map n->dot-struct-string gl32-integers))

(define (gl32-family->dot-struct-string ns)
  (string-append
   (~a (car ns))
   " [label=\""
   (string-join (map (λ (n) (matrix-list->dot-struct-string (n->matrix-list n))) ns) "|{&nbsp;&nbsp;}|")
   "\"];"))


(check-equal? (gl32-family->dot-struct-string '(98)) "98 [label=\"{ | |█}|{█| | }|{ |█| }\"];")

;(for-each displayln (map gl32-family->dot-struct-string (remove-duplicates (vector->list-not-0 gl32-families-as-ns-vector))))
;(for-each displayln (map family-triangle->string gl32-families-graph-triangles))
;(for-each displayln (map family-cycle->string gl32-families-graph-not-triangles))

;;;;;;;;;;;;;;;;;
; metapost functions

(define metapost-vars-array (array #[#[#["O" "Z"] #["Y" "YpZ"]] #[#["X" "XpZ"] #["XpY" "XpYpZ"]]]))

(define triples (cartesian-product '(0 1) '(0 1) '(0 1)))
(check-equal? triples '((0 0 0) (0 0 1) (0 1 0) (0 1 1) (1 0 0) (1 0 1) (1 1 0) (1 1 1)))

(check-equal?
 (map (λ(_) (array-ref metapost-vars-array (list->vector _)))
      triples)
 '("O" "Z" "Y" "YpZ" "X" "XpZ" "XpY" "XpYpZ"))

(check-equal? (array-ref metapost-vars-array '#[0 1 1]) "YpZ")

(define (triple-vectors gl32-matrix triple)
  (let* ((triple-matrix (list->matrix 3 1 triple))
         (image-matrix (gl32-matrix* (matrix-transpose gl32-matrix) triple-matrix)))
      (cons (list->vector triple) (matrix->vector image-matrix))))

(define (y-sum triple-vector-pair)
  (+ (vector-ref (car triple-vector-pair) 1)
     (vector-ref (cdr triple-vector-pair) 1)))

(check-equal? (y-sum '(#(0 0 1) . #(1 0 1))) 0)
(check-equal? (y-sum '(#(0 1 1) . #(1 1 1))) 2)

(define (sort-by-Y-desc triple-vector-pairs)
  (sort triple-vector-pairs
        (λ (p1 p2) (> (y-sum p1) (y-sum p2)))))

(check-equal?
 (let1 matrix85 (n->gl32-matrix 85)
       (sort-by-Y-desc
        (filter (λ (_) (not (equal? (car _) (cdr _))))
                (map (λ (_) (triple-vectors matrix85 _))
                     triples))))
 '((#(0 1 1) . #(1 1 1))
   (#(1 1 0) . #(0 1 1))
   (#(1 1 1) . #(1 1 0))
   (#(0 0 1) . #(1 0 1))
   (#(1 0 0) . #(0 0 1))
   (#(1 0 1) . #(1 0 0))))

(define (metapost-dot-line triple-vector-pairs)
  (string-append "  draw_arrow_pairs("
                 (array-ref metapost-vars-array (car triple-vector-pairs))
                 ", "
                 (array-ref metapost-vars-array (cdr triple-vector-pairs))
                 ", margin);"))

(define (metapost-dot n)
  (let1 matrix (n->gl32-matrix n)
        (string-append "  draw_dots("
                       (string-join
                        (map
                         (λ(_)
                           (array-ref metapost-vars-array
                                      (matrix->vector
                                       (gl32-matrix*
                                        (matrix-transpose matrix)
                                        (list->matrix 3 1 _)))))
                         (cdr triples))
                        ", ")
                       ");")))
  


(define (display-metapost-gl32-figure n)
  (let1 matrix (n->gl32-matrix n)
        (displayln (string-append "beginfig(" (~a n) ");"))
        (for-each displayln
                  (map metapost-dot-line
                       (sort-by-Y-desc
                        (filter (λ (_) (not (equal? (car _) (cdr _))))
                                (map (λ (_) (triple-vectors matrix _))
                                     triples)))))
        (displayln (metapost-dot n))
        (displayln "endfig;")))

;(for-each display-metapost-gl32-figure gl32-integers)
