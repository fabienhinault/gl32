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

(define (n->gl32-object n)
  (list (cons 'n n) (cons 'matrix (get-gl32-matrix n))))

(define (gl32-matrix->n m)
  (let1 l (matrix->list m)
        (bit-list->n l 9 0)))

(check-equal? (gl32-matrix->n (matrix [[0 0 0] [0 0 0] [0 0 0]])) 0)
(check-equal? (gl32-matrix->n (matrix [[0 0 0] [0 0 0] [0 0 1]])) 1)
(check-equal? (gl32-matrix->n (matrix [[0 0 1] [0 1 0] [1 0 0]])) 84)
  

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

(define (gl32-transpose gl32-object)
  (matrix->gl32 (matrix-transpose (cdr (assoc 'matrix gl32-object)))))

(define gl32-integers (map (λ (_) (cdr (assoc 'n _))) gl32-objects))

(define (gl32-matrix* m1 m2)
  (matrix-map mod2 (matrix* m1 m2)))

; powers of a GL32 matrix
(define (get-gl32-powers m result)
  (let1 next (gl32-matrix* (car result) m)
        (if (equal? m next)
            (reverse (cdr result))
            (get-gl32-powers m (cons next result)))))

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
                (ps (get-gl32-powers m (list m)))
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

(define transitions
   (map list->gl32
        '((0 1 0  1 0 0  0 0 1)
          (0 0 1  0 1 0  1 0 0)
          (1 0 0  0 0 1  0 1 0)
          (0 0 1  1 0 0  0 1 0)
          (0 1 0  0 0 1  1 0 0))))

; same as transition-matrices, just swapping two last ones
(define transition-inverses
   (map list->gl32
        '((0 1 0  1 0 0  0 0 1)
          (0 0 1  0 1 0  1 0 0)
          (1 0 0  0 0 1  0 1 0)
          (0 1 0  0 0 1  1 0 0)
          (0 0 1  1 0 0  0 1 0))))

(define gl32-families-vector (make-vector 512))

(define (build-family gl32-object)
  (let1 permuted-objects (map (λ (_1 _2) (gl32* _1 gl32-object _2))
                               transition-inverses
                               transitions)
        (remove-duplicates (cons gl32-object (append permuted-objects (map gl32-transpose permuted-objects))))))

(for-each (λ (_) (vector-set! gl32-families-vector
                              (cdr (assoc 'n _))
                              (build-family _)))
          gl32-objects)

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