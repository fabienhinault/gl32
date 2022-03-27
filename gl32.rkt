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

(define (mod2 n)
  (modulo n 2))

(define (length< l1 l2)
  (< (length l1) (length l2)))

(define (vector->list-not-0 v)
  (vector->list (vector-filter (λ (_) (not (equal? 0 _))) v)))

(define (bit-list n size result)
  (if (equal? size 0)
      result
      (bit-list (arithmetic-shift n -1) (- size 1) (cons (bitwise-bit-field n 0 1) result)))) 

(check-equal? (bit-list 0 9 '())   '(0 0 0  0 0 0  0 0 0))
(check-equal? (bit-list 1 9 '())   '(0 0 0  0 0 0  0 0 1))
(check-equal? (bit-list 511 9 '()) '(1 1 1  1 1 1  1 1 1))

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
  (group-by-n (bit-list n 9 '()) 3 '()))

(define (get-gl32-matrix n)
  (list->matrix 3 3 (bit-list n 9 '())))

(check-equal? (get-gl32-matrix 0)   (matrix [[0 0 0] [0 0 0] [0 0 0]]))
(check-equal? (get-gl32-matrix 1)   (matrix ((0 0 0) (0 0 0) (0 0 1))))
;84 = 64 + 16 + 4 = 2**6 + 2**4 + 2**2
(check-equal? (get-gl32-matrix 84)  (matrix ((0 0 1) (0 1 0) (1 0 0))))

(define (gl32-matrix->n m)
  (let1 l (matrix->list m)
        (bit-list->n l 9 0)))

(check-equal? (gl32-matrix->n (matrix [[0 0 0] [0 0 0] [0 0 0]])) 0)
(check-equal? (gl32-matrix->n (matrix [[0 0 0] [0 0 0] [0 0 1]])) 1)
(check-equal? (gl32-matrix->n (matrix [[0 0 1] [0 1 0] [1 0 0]])) 84)
  
(define (gl32-matrix* m1 m2)
  (matrix-map mod2 (matrix* m1 m2)))

; powers of a GL32 matrix
(define (get-gl32-matrix-powers m result)
  (let1 next (gl32-matrix* (car result) m)
        (if (equal? m next)
            (reverse (cdr result))
            (get-gl32-matrix-powers m (cons next result)))))


;;;;;;;
; gl32 objects

(define (n->gl32-object n)
  (list (cons 'n n) (cons 'matrix (get-gl32-matrix n))))

(define gl32-identity (n->gl32-object 273))

(define _84 (n->gl32-object 84))
(define _85 (n->gl32-object 85))
(define _86 (n->gl32-object 86))
(define _98 (n->gl32-object 98))
(define _140 (n->gl32-object 140))

(define (get-n o)
  (cdr (assoc 'n o)))

(define (get-matrix o)
  (cdr (assoc 'matrix o)))

; M_3(ZZ_2) the set of all square matrices of dimension 3 in ZZ_2
(define m3z2 (map n->gl32-object (range 0 512)))
(define m3z2-vector (apply vector m3z2))
;list of GL32 objects
(define gl32-objects (filter (λ (_) (odd? (matrix-determinant (cdr (assoc 'matrix _))))) m3z2))
(define gl32-vector (vector-map (λ (_) (if (odd? (matrix-determinant (cdr (assoc 'matrix _)))) _ 0)) m3z2-vector))

(check-equal? (length gl32-objects) 168)

(define (matrix->gl32 m)
  (let1 mm2 (matrix-map mod2 m) 
        (list (cons 'n (gl32-matrix->n mm2)) (cons 'matrix mm2))))

(define (list->gl32 l)
  (matrix->gl32 (list->matrix 3 3 l)))

(define (gl32* . gl32s)
  (matrix->gl32 (apply matrix* (map (λ (_) (cdr (assoc 'matrix _))) gl32s))))

(define (gl32-square o)
  (gl32* o o))

(define (gl32-transpose gl32-object)
  (matrix->gl32 (matrix-transpose (cdr (assoc 'matrix gl32-object)))))

(define (gl32-symetrical? gl32-object)
  (matrix= (get-matrix gl32-object) (matrix-transpose (get-matrix gl32-object))))

(check-true (gl32-symetrical? (n->gl32-object 273)))
(check-true (gl32-symetrical? (n->gl32-object 84)))
(check-true (gl32-symetrical? (n->gl32-object 85)))
(check-false (gl32-symetrical? _86))

(define gl32-integers (map (λ (_) (cdr (assoc 'n _))) gl32-objects))

;F8
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

(define (f8-object vector symbol power)
  (let1 alist (list (cons 'vector vector)
                    (cons 'vector-n (f8-vector->n vector))
                    (cons 'symbol symbol)
                    (cons 'power power)
                    (cons 'ref0? (λ (i) (equal? 0 (vector-ref vector i)))))
        (λ (arg) (cdr (assoc arg alist)))))
(define (f8==? _1 _2)
  (equal? (_1 'vector) (_2 'vector)))

(define _f8-0 (f8-object #[0 0 0] '0 '∞))
(define _f8-1 (f8-object #[1 0 0] '1 '0))
(define _f8-X (f8-object #[0 1 0] 'X '1))
(define _f8-X2 (f8-object #[0 0 1] 'X2 '2))
(define _f8-X+1 (f8-object #[1 1 0] 'X+1 '3))
(define _f8-X2+X (f8-object #[0 1 1] 'X2+X '4))
(define _f8-X2+X+1 (f8-object #[1 1 1] 'X2+X+1 '5))
(define _f8-X2+1 (f8-object #[1 0 1] 'X2+1 '6))

(check-equal? (_f8-X2+1 'vector) #[1 0 1])
(check-true (f8==? _f8-0 (f8-object #[0 0 0] '0 '∞)))
(check-true ((_f8-X2+1 'ref0?) 1))
(check-false ((_f8-X2+1 'ref0?) 0))
(check-false ((_f8-X2+1 'ref0?) 2))

(define f8-powers (vector _f8-1 _f8-X _f8-X2 _f8-X+1 _f8-X2+X _f8-X2+X+1 _f8-X2+1))

(define f8-vectors (make-vector 8))
(vector-set! f8-vectors 0 _f8-0)
(for-each
 (λ (_) (vector-set! f8-vectors (f8-vector->n (_ 'vector)) _))
 (vector->list f8-powers))
(check-true (f8==? (vector-ref f8-vectors 6) _f8-X2+X))


(define (f8+ . f8s)
  (vector-ref f8-vectors (f8-vector->n (vector-map mod2 (foldl (λ vs (apply vector-map + vs)) #[0 0 0] (map (λ (_) (_ 'vector)) f8s))))))
(check-true (f8==? (f8+ _f8-0 _f8-0) _f8-0))
(check-true (f8==? (f8+ _f8-0 _f8-1) _f8-1))
(check-true (f8==? (f8+ _f8-X _f8-0) _f8-X))
(check-true (f8==? (f8+ _f8-X2+X+1 _f8-X2+1) _f8-X))

(define (_f8*powers power1 power2)
  (vector-ref f8-powers (+ power1 power2)))

(define (f8* _1 _2)
  (if (or (f8==? _1 _f8-0) (f8==? _2 _f8-0))
      _f8-0
      (apply f8+ (flatten (map (λ (i1)
                                 (map (λ (i2)
                                        (if (or ((_1 'ref0?) i1) ((_2 'ref0?) i2))
                                            _f8-0
                                            (_f8*powers i1 i2)))
                                      (range 3)))
                               (range 3))))))
(check-true (f8==? (f8* _f8-0 _f8-0) _f8-0))
(check-true (f8==? (f8* _f8-0 _f8-1) _f8-0))
(check-true (f8==? (f8* _f8-X _f8-0) _f8-0))
(check-true (f8==? (f8* _f8-1 _f8-1) _f8-1))
(check-true (f8==? (f8* _f8-X _f8-1) _f8-X))
(check-true (f8==? (f8* _f8-1 _f8-X2) _f8-X2))
(check-true (f8==? (f8* _f8-X2+X+1 _f8-X2+1) _f8-X2+X))

(define (gl32-f8 ogl32 of8)
  (vector-ref
   f8-vectors
   (f8-vector->n (matrix->vector (gl32-matrix* (get-matrix ogl32) (vector->matrix 3 1 (of8 'vector)))))))

(check-true (f8==? (gl32-f8 _84 _f8-0) _f8-0))
(check-true (f8==? (gl32-f8 _84 _f8-1) _f8-X2))
(check-true (f8==? (gl32-f8 _84 _f8-X2) _f8-1))
(check-true (f8==? (gl32-f8 _84 _f8-X+1) _f8-X2+X))
(check-true (f8==? (gl32-f8 _84 _f8-X2+X) _f8-X+1))
(check-true (f8==? (gl32-f8 _84 _f8-X) _f8-X))
(check-true (f8==? (gl32-f8 _84 _f8-X2+1) _f8-X2+1))
(check-true (f8==? (gl32-f8 _84 _f8-X2+X+1) _f8-X2+X+1))

(check-true (f8==? (gl32-f8 _85 _f8-0) _f8-0))
(check-true (f8==? (gl32-f8 _85 _f8-1) _f8-X2))
(check-true (f8==? (gl32-f8 _85 _f8-X2) _f8-X2+1))
(check-true (f8==? (gl32-f8 _85 _f8-X2+1) _f8-1))
(check-true (f8==? (gl32-f8 _85 _f8-X) _f8-X))
(check-true (f8==? (gl32-f8 _85 _f8-X+1) _f8-X2+X))
(check-true (f8==? (gl32-f8 _85 _f8-X2+X) _f8-X2+X+1))
(check-true (f8==? (gl32-f8 _85 _f8-X2+X+1) _f8-X+1))

;SL(2,7)



; powers of a GL32 object
(define (_get-gl32-powers gl32-object result)
  (let1 next (gl32* (car result) gl32-object)
        (if (equal? gl32-identity next)
            (reverse result)
            (_get-gl32-powers gl32-object (cons next result)))))

(check-equal? (length (_get-gl32-powers _84 (list _84))) 1)

(define (get-gl32-powers gl32-object)
  (_get-gl32-powers gl32-object (list gl32-object)))

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
         (let* ((m (cdr(assoc 'matrix _)))
                (ps (get-gl32-matrix-powers m (list m)))
                (ns (map gl32-matrix->n ps)))
           (list (cdr(assoc 'n _)) (length ns) ns )))
       gl32-objects))


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
; families

(define transitions
   (map list->gl32
        '((0 1 0  1 0 0  0 0 1)
          (0 0 1  0 1 0  1 0 0)
          (1 0 0  0 0 1  0 1 0)
          (0 0 1  1 0 0  0 1 0)
          (0 1 0  0 0 1  1 0 0))))

; same as transition-matrices, just swapping two last ones
(define transitions-inverses
   (map list->gl32
        '((0 1 0  1 0 0  0 0 1)
          (0 0 1  0 1 0  1 0 0)
          (1 0 0  0 0 1  0 1 0)
          (0 1 0  0 0 1  1 0 0)
          (0 0 1  1 0 0  0 1 0))))

(define (check-inverses ts tis)
  (for-each
   (λ (_orig _inverse)
     (check-equal? (matrix-map mod2 (matrix-inverse (get-matrix _orig)))
                   (get-matrix _inverse)))
   ts
   tis))

(check-inverses transitions transitions-inverses)

(define (get-permuted-objects gl32-object tis ts)
  (map (λ (_1 _2) (gl32* _1 gl32-object _2))
       tis
       ts))

(define (get-all-permuted-objects gl32-object)
  (get-permuted-objects gl32-object transitions-inverses transitions))


(define (_build-family result-objects
                      result-transitions
                      result-transitions-inverses
                      powers
                      permuted-objects
                      remaining-transitions
                      remaining-transitions-inverses)
  (if (no? permuted-objects)
      (begin
        (check-inverses result-transitions result-transitions-inverses)
        (list (cons 'transitions (reverse result-transitions))
              (cons 'transitions-inverses (reverse result-transitions-inverses))
              (cons 'gl32s
                    (reverse
                     (if (member (gl32-transpose (car result-objects)) powers)
                         result-objects
                         (append (map gl32-transpose result-objects) result-objects))))))
      (let1 next (car permuted-objects)
            (if (member next powers)
                (_build-family result-objects
                               result-transitions
                               result-transitions-inverses
                               powers
                               (cdr permuted-objects)
                               (cdr remaining-transitions)
                               (cdr remaining-transitions-inverses))
                (_build-family (cons next result-objects)
                              (cons (car remaining-transitions) result-transitions)
                              (cons (car remaining-transitions-inverses) result-transitions-inverses)
                              (append powers (_get-gl32-powers next (list next)))
                              (cdr permuted-objects)
                              (cdr remaining-transitions)
                              (cdr remaining-transitions-inverses))))))

(define (build-family gl32-object)
  (_build-family (list gl32-object)
                      '()
                      '()
                      (_get-gl32-powers gl32-object (list gl32-object))
                      (get-all-permuted-objects gl32-object)
                      transitions
                      transitions-inverses))

  
(define gl32-family-identity (list (cons 'gl32s (list gl32-identity)) (cons 'transitions '())))

; gl32 family getters
(define (get-gl32s family) (cdr (assoc 'gl32s family)))
(define (get-transitions family) (cdr (assoc 'transitions family)))
(define (get-transitions-inverses family) (cdr (assoc 'transitions-inverses family)))
(define (gl32-family-symetrical? family) (gl32-symetrical? (car (get-gl32s family))))
(define (gl32-family->ns family) (map get-n (get-gl32s family)))


(check-equal? (get-gl32s (build-family _98)) (list _98))

(define (gl32-family* f1 f2)
  (check-equal? (get-transitions f1) (get-transitions f2))
  (check-equal? (get-transitions-inverses f1) (get-transitions-inverses f2))
  (let* ((first1 (car (get-gl32s f1)))
         (first2 (car (get-gl32s f2)))
         (first1*2 (gl32* first1 first2)))
    (if (equal? first1*2 gl32-identity)
        (begin
          (for-each (λ (o1 o2) (check-equal? (gl32* o1 o2) gl32-identity)) (cdr (get-gl32s f1)) (cdr (get-gl32s f2)))
          gl32-family-identity)
        (let1 result (_build-family (list first1*2) '() '()
                                   (_get-gl32-powers first1*2 (list first1*2))
                                   (get-permuted-objects first1*2 (get-transitions-inverses f1) (get-transitions f1))
                                   (get-transitions f1)
                                   (get-transitions-inverses f1))
              (check-equal? (length (get-gl32s result)) (length (get-gl32s f1))
                            (string-append "not same length: " (~a f1) "\n" (~a result)))
              (for-each
               (λ (o1 o2 o-result)
                 (check-equal? (gl32* o1 o2) o-result
                               (string-append
                                "wrong product in: "
                                (~a (get-n (car (get-gl32s f1))))
                                " * "
                                (~a (get-n (car (get-gl32s f2))))
                                "\n"
                                (~a result))))
               (get-gl32s f1)
               (get-gl32s f2)
               (get-gl32s result))
              result))))


(let* ((_84  (n->gl32-object 84))
       (__84 (_build-family (list _84) '() '()
                            (get-all-permuted-objects _84)
                            (_get-gl32-powers _84 (list _84))
                            transitions
                            transitions-inverses)))
      (check-equal? gl32-family-identity  (gl32-family* __84 __84)))

(let* ((_86  (n->gl32-object 86))
       (_403 (n->gl32-object 403))
       (transitions (list (n->gl32-object 161)  (n->gl32-object 266)))
       (__86 (build-family  _86)))
      (check-equal?
       (gl32-family* __86 __86)
       (_build-family (list _403) '() '() (get-gl32-powers _403) (get-permuted-objects _403 transitions transitions) transitions transitions)))
  

; powers of a GL32 family
(define (get-gl32-family-powers f result)
  (let1 next (gl32-family* (car result) f)
        (if (equal? gl32-family-identity next)
            (reverse result)
            (get-gl32-family-powers f (cons next result)))))

(define (vector-set-family! vf f vl l vc fp)
  (for-each
   (λ (gl32-object)
     (let1 n (get-n gl32-object)
           (when (< (vector-ref vl n) l)
             (vector-set! vf n f)
             (vector-set! vl n l)
             (vector-set! vc n fp))))
   (get-gl32s f)))

(define (vector-set-family-powers-to-family-vector! vf vc fp vl)
  (let1 l (length fp)
        (for-each
         (λ (family) (vector-set-family! vf family vl l vc fp))
         fp)))

(define gl32-families-vector (make-vector 512))
(define gl32-families-cycles-vector (make-vector 512))
(define gl32-families-lengths-vector (make-vector 512))
(for-each
 (λ (gl32-object)
   (let* ((n (cdr (assoc 'n gl32-object)))
          (fp (get-gl32-family-powers (build-family gl32-object) (list (build-family gl32-object))))
          (l (length fp)))
     (vector-set-family-powers-to-family-vector! gl32-families-vector
                                                 gl32-families-cycles-vector
                                                 fp
                                                 gl32-families-lengths-vector)))
 gl32-objects)

(define gl32-families-as-ns-vector
  (vector-map
   (λ (_) (if (equal? _ 0) 0 (gl32-family->ns _)))           
   gl32-families-vector))


(define gl32-families-cycles-as-ns-vector
  (vector-map
   (λ (cycle) (if (equal? cycle 0) 0 (map gl32-family->ns cycle)))         
   gl32-families-cycles-vector))

(define gl32-families-graph-cycles
  (remove-duplicates
   (vector->list
    (vector-filter (λ (_) (not (equal? 0 _))) gl32-families-cycles-as-ns-vector))))

(define gl32-families-graph-triangles
  (filter (λ (_) (equal? 2 (length _))) gl32-families-graph-cycles))

(define gl32-families-graph-not-triangles
  (sort (filter (λ (_) (< 2 (length _))) gl32-families-graph-cycles) length<))

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

(define (row->dot-struct-string row)
  (string-append
   "{"
   (string-join (map (λ (_) (vector-ref dot-struct-string-replacement-vector _))
                     row)
                "|")
   "}"))

(check-equal? (row->dot-struct-string '(0 1 0)) "{ |█| }")

(define (matrix-list->dot-struct-string matrix-list)
  (string-join (map row->dot-struct-string matrix-list) "|"))

(define (n->dot-struct-string n)
  (string-append
   (~a n)
   " [label=\""
   (matrix-list->dot-struct-string (n->matrix-list n))
   "\"];"))

(check-equal? (n->dot-struct-string 98) "98 [label=\"{ | |█}|{█| | }|{ |█| }\"];")

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
 (let1 matrix85 (get-gl32-matrix 85)
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

(define (display-metapost-gl32-figure n)
  (let1 matrix (get-gl32-matrix n)
        (displayln (string-append "beginfig(" (~a n) ");"))
        (displayln "  draw_dots;")
        (for-each displayln
                  (map metapost-dot-line
                       (sort-by-Y-desc
                        (filter (λ (_) (not (equal? (car _) (cdr _))))
                                (map (λ (_) (triple-vectors matrix _))
                                     triples)))))
        (displayln "endfig;")))

;(for-each display-metapost-gl32-figure gl32-integers)