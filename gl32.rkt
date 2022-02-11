#lang racket

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

(define (get-n o)
  (cdr (assoc 'n o)))

(define (get-matrix o)
  (cdr (assoc 'matrix o)))


(define m3z2 (map n->gl32-object(range 0 512)))
;list of GL32 objects
(define gl32-objects (filter (λ (_) (not (equal? 0 (with-modulus 2 (mod (matrix-determinant (cdr(assoc 'matrix _)))))))) m3z2))

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

; for each integer i corresponding to a matrix in GL(3,2), (vector-ref gl32-indices-vector i)
; will be the index of the first-found longest cycle
;> gl32-indices-vector
;'#(0
;   ...
;   0
;   254  ; at rank 84
;   ...
;   494  ; at rank 501
;   0
;   ...
;   0)
(define gl32-indices-vector (make-vector 512))

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

; build gl32-indices-vector gl32-lengths-vector
(for-each (λ (_) (add-cycle! _ gl32-indices-vector gl32-lengths-vector))
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
         (vector-filter (λ (_) (not (equal? 0 _))) gl32-indices-vector)))))

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
                     (if (member (gl32-transpose (car result-objects)) result-objects)
                         result-objects
                         (append (map gl32-transpose result-objects) result-objects))))))
      (let1 next (car permuted-objects)
            (if (member next powers)
                (_build-family result-objects
                              result-transitions
                              result-transitions-inverses
                              powers (cdr permuted-objects)
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


(define (gl32-family* f1 f2)
  (check-equal? (get-transitions f1) (get-transitions f2))
  (check-equal? (get-transitions-inverses f1) (get-transitions-inverses f2))
  (let* ((first1 (car (get-gl32s f1)))
         (first2 (car (get-gl32s f2)))
         (first1*2 (gl32* first1 first2)))
    (if (equal? first1*2 gl32-identity)
        gl32-family-identity
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
                               (string-append "wrong product in: " (~a (get-n (car (get-gl32s f1)))) " * " (~a (get-n (car (get-gl32s f2)))) "\n" (~a result))))
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

(define (cycle->string cycle-list)
  (string-append "273 -- " (string-join (map ~a cycle-list) " -- ") ";"))

(define (triangle->string triangle-list)
  (string-append (string-join (map ~a (reverse triangle-list)) " -- ") " -- 273;"))


(for-each displayln (map triangle->string gl32-graph-triangles))
(for-each displayln (map cycle->string gl32-graph-not-triangles))

(define dot-struct-string-replacement-vector (vector " " "█"))

(define (row->dot-struct-string row)
  (string-append
   "{"
   (string-join (map (λ (_) (vector-ref dot-struct-string-replacement-vector _))
                     row)
                "|")
   "}"))

(check-equal? (row->dot-struct-string '(0 1 0)) "{ |█| }")

(define (n->dot-struct-string n)
  (let1 matrix-list (n->matrix-list n)
        (string-append
         (~a n)
         " [label=\""
         (string-join (map row->dot-struct-string matrix-list) "|")
         "\"];")))

(for-each displayln
          (map n->dot-struct-string gl32-integers))


(define metapost-vars-array (array #[#[#["O" "Z"] #["Y" "YpZ"]] #[#["X" "XpZ"] #["XpY" "XpYpZ"]]]))

(define triples (cartesian-product '(0 1) '(0 1) '(0 1)))

(check-equal? (array-ref metapost-vars-array '#[0 1 1]) "YpZ")

(define (metapost-dot-line gl32-matrix triple)
  (let* ((triple-matrix (list->matrix 3 1 triple))
         (triple-vector (list->vector triple))
         (image-matrix (gl32-matrix* (matrix-transpose gl32-matrix) triple-matrix))
         (image-vector (matrix->vector image-matrix)))
    (when (not (equal? triple-matrix image-matrix))
      (displayln
       (string-append "  draw_arrow_pairs("
                      (array-ref metapost-vars-array triple-vector)
                      ", "
                      (array-ref metapost-vars-array image-vector)
                      ", margin);")))))

(define (display-metapost-gl32-figure n)
  (displayln (string-append "beginfig(" (~a n) ");"))
  (displayln "  draw_dots;")
  (for-each (λ (_) (metapost-dot-line (get-gl32-matrix n) _))
            triples)
  (displayln "endfig;"))

(for-each display-metapost-gl32-figure gl32-integers)