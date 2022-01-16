#lang racket

(require math/number-theory)
(require math/matrix)
(require rackunit)

(define-syntax-rule (let1 a b body ...)
  (let ((a b)) body ...))

(define (no? l)
  (equal? l '()))

(define (bit-list n size result)
  (if (equal? size 0)
      result
      (bit-list (arithmetic-shift n -1) (- size 1) (cons (bitwise-bit-field n 0 1) result)))) 

(check-equal? (bit-list 0 9 '())   '(0 0 0 0 0 0 0 0 0))
(check-equal? (bit-list 1 9 '())   '(0 0 0 0 0 0 0 0 1))
(check-equal? (bit-list 511 9 '()) '(1 1 1 1 1 1 1 1 1))

(define (bit-list->n list len result)
  (if (no? list)
      result
      (bit-list->n (cdr list) (- len 1) (+ (* 2 result) (car list)))))

(check-equal? (bit-list->n '(0 0 0 0 0 0 0 0 0) 9 0) 0)
(check-equal? (bit-list->n '(0 0 0 0 0 0 0 0 1) 9 0) 1)
(check-equal? (bit-list->n '(1 1 1 1 1 1 1 1 1) 9 0) 511)

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

(define (get-gl32-object n)
  (list (cons 'n n) (cons 'matrix (get-gl32-matrix n))))

(define (gl32-matrix->n m)
  (let1 l (matrix->list m)
        (bit-list->n l 9 0)))

(check-equal? (gl32-matrix->n (matrix [[0 0 0] [0 0 0] [0 0 0]])) 0)
(check-equal? (gl32-matrix->n (matrix [[0 0 0] [0 0 0] [0 0 1]])) 1)
(check-equal? (gl32-matrix->n (matrix [[0 0 1] [0 1 0] [1 0 0]])) 84)
  

(define m3z2 (map get-gl32-object(range 0 512)))
(define gl32 (filter (λ (_) (not (equal? 0 (with-modulus 2 (mod (matrix-determinant (cdr(assoc 'matrix _)))))))) m3z2))

(check-equal? (length gl32) 168)

(define gl32-integers (map (λ (_) (cdr(assoc 'n _))) gl32))

(define (gl32* m1 m2)
  (with-modulus 2 (matrix-map mod (matrix* m1 m2))))

(define (get-gl32-powers m result)
  (let1 next (gl32* (car result) m)
        (if (equal? m next)
            (reverse (cdr result))
            (get-gl32-powers m (cons next result)))))

(define powers
  (map (λ (_)
         (let* ((m (cdr(assoc 'matrix _)))
                (ps (get-gl32-powers m (list m)))
                (ns (map gl32-matrix->n ps)))
           (list (cdr(assoc 'n _)) (length ns) ns )))
       gl32))


(define gl32-cycles-vector (make-vector 512))
(for-each (λ (_) (vector-set! gl32-cycles-vector (car _) (caddr _)))
     powers)

(define (add-cycle-element! cycle-element cycle-index cycle-length cycles-vector lengths-vector)
  (when (< (vector-ref lengths-vector cycle-element) cycle-length)
    (vector-set! cycles-vector cycle-element cycle-index)
    (vector-set! lengths-vector cycle-element cycle-length)))

(define (add-cycle! cycle indices-vector lengths-vector)
  (map (λ (_)
         (add-cycle-element! _ (car cycle) (cadr cycle) indices-vector lengths-vector))
       (caddr cycle)))

(define gl32-indices-vector (make-vector 512))
(define gl32-lengths-vector (make-vector 512))
(for-each (λ (_) (add-cycle! _ gl32-indices-vector gl32-lengths-vector))
     powers)

(define gl32-graph-cycles
  (map (λ (_) (vector-ref gl32-cycles-vector _))
       (remove-duplicates
        (vector->list
         (vector-filter (λ (_) (not (equal? 0 _))) gl32-indices-vector)))))


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
