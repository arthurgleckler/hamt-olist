;;;; Persistent Ordered List (POL)

;;; Copyright MMXX Arthur A. Gleckler.  All rights reserved.

(declare (usual-integrations))

;;; Public protocol (API)

;; (pol? datum)

;;    Return true iff `datum' is a persistent ordered list.

;; (make-persistent-ordered-list hash = [data])

;;   Return a new immutable persistent ordered list that uses the `hash'
;;   procedure to hash its elements and `=' to compare them.  If list `data' is
;;   supplied, include all its data in the result.  Later occurrences of the
;;   same element override earlier ones.  The same element cannot appear in the
;;   list more than once, and no element may be #f.

;; (pol/count pol)

;;   Return the number of elements in `pol'.

;; (pol/empty? pol)

;;   Return true iff `pol' is empty.

;; (pol/contains? pol datum)

;;   Return true iff `pol' contains `datum'.

;; (pol/fold procedure seed pol)

;;   Fold `procedure' over `pol' in forward order.  `Procedure' expects its
;;   accumulator in its second argument.  The accumulator starts with `seed'.

;; (pol/fold-right procedure seed pol)

;;   Fold `procedure' over `pol' in backward order.  `Procedure' expects its
;;   accumulator in its second argument.  The accumulator starts with `seed'.

;; (pol->forward-list pol)

;;   Return `pol' as a list in forward order.

;; (pol->backward-list pol)

;;   Return `pol' as a list in backward order.

;; (pol/mutable pol)

;;   Return a mutable copy of `pol'.  Changes to the copy will not affect `pol'.
;;   Mutable POLs have better constant factors for updates, but are less
;;   compact.

;; (pol/immutable pol)

;;   Return an immutable copy of `pol'.  Changes to `pol' will not affect the
;;   copy.  Immutable POLs are more compact, but slower to update.

;; (pol/push pol datum)

;;   Add `datum' to the end of `pol' without mutation, returning a new POL.

;; (pol/push! pol datum)

;;   Destructively add `datum' to the end of `pol'.

;; (pol/pop pol)

;;   Without mutating `pol', return both the last element in `pol' and `pol'
;;   without that element.  Signal an error if `pol' is empty.

;; (pol/pop! pol)

;;   Destructively remove the last element from `pol' and return it.  Signal an
;;   error if `pol' is empty.

;;; Representation

;; Each POL (persistent ordered list) is represented by a record consisting of
;; three parts: a HAMT (Hash-Array Mapped Trie), the first value, and the last
;; value.  Each element of the HAMT maps an element of the POL to a pair of the
;; previous and next element, or #f when there is none.

(define-record-type ordered-list
    (%make-persistent-ordered-list first last hamt)
    pol?
  (first pol/first set-pol/first!)
  (hamt pol/hamt)
  (last pol/last set-pol/last!))

(define (make-pol-hamt = hash)
  (make-hamt = hash #t))

(define ((pol/adjacent choose) hamt datum)
  (choose (hamt-fetch hamt datum)))

(define pol/previous (pol/adjacent car))
(define pol/next (pol/adjacent cdr))

(define (pol-remove! hamt datum)
  "Return `datum' from the `HAMT' of a POL.  Return two values, X and Y.  If the
first element of the POL changed as a result, X is the new first element;
otherwise, it is #f.  If `datum' is removed, Y is the element that was before
it, if any; otherwise, it is #f."
  (let ((previous-next (hamt-fetch hamt datum)))
    (if (hamt-null? previous-next)
	(values #f #f)
	(let* ((previous (car previous-next))
	       (next (cdr previous-next))
	       (previous* (and previous (pol/previous hamt previous)))
	       (next* (and next (pol/next hamt next))))
	  (when previous
	    (hamt/put! hamt previous (cons previous* next)))
	  (when next
	    (hamt/put! hamt next (cons previous next*)))
	  (values (and (not previous) next) previous)))))

(define make-persistent-ordered-list
  (case-lambda
   ((hash =) (make-persistent-ordered-list hash = '()))
   ((hash = data)
    (if (null? data)
	(%make-persistent-ordered-list #f #f (make-pol-hamt = hash))
	(let ((data data)
	      (hamt (hamt/mutable (make-pol-hamt = hash))))
	  (let push ((data data)
		     (first #f)
		     (previous #f))
	    (if (null? data)
		(%make-persistent-ordered-list first
					       previous
					       (hamt/immutable hamt))
		(let ((datum (car data))
		      (next (and (not (null? (cdr data)))
				 (cadr data))))
		  (assert datum "No element may be #f.")
		  (if (and next (= datum next))
		      (push (cdr data) first previous)
		      (let-values (((first* previous*)
				    (pol-remove! hamt datum)))
			(hamt/put! hamt datum (cons previous next))
			(push (cdr data)
			     (or first* first datum)
			     datum)))))))))))

(define (pol/count pol)
  (hamt/count (pol/hamt pol)))

(define-test-group (pol/count)
  (let ((terrible-hash (lambda (x) x)))
    (lambda (expected input)
      (assert
       (= expected
	  (pol/count (make-persistent-ordered-list terrible-hash = input))))))
  '(0 ())
  '(1 (1))
  '(1 (1 1))
  '(2 (1 2))
  '(3 (3 1 2))
  '(3 (3 1 2 3))
  '(2 (1 1 2))
  '(2 (1 2 2))
  '(3 (1 1 2 2 3 3)))

(define (pol/empty? pol)
  "Return true iff `pol' is empty."
  (zero? (pol/count pol)))

(define (pol/contains? pol datum)
  "Return true iff `pol' contains `datum'."
  (not (hamt-null? (hamt-fetch pol datum))))

(define ((pol-folder extremum previous) procedure seed pol)
  (if (pol/empty? pol)
      seed
      (let* ((hamt (pol/hamt pol))
	     (end (extremum pol)))
	(let fold ((accumulator (list end))
		   (element end))
	  (let ((datum (previous (hamt-fetch hamt element))))
	    (if datum
		(fold (procedure datum accumulator)
		      datum)
		accumulator))))))

;; Fold over `pol' in forward and backward order, respectively.
(define pol/fold (pol-folder pol/first cdr))
(define pol/fold-right (pol-folder pol/last car))

(define (pol->list extremum previous)
  (let ((fold (pol-folder extremum previous)))
    (lambda (pol) (fold cons '() pol))))

;; Return `pol' as a list in forward and backward order, respectively.
(define pol->forward-list (pol->list pol/last car))
(define pol->backward-list (pol->list pol/first cdr))

(define-test-group (pol->forward-list)
  (let ((terrible-hash (lambda (x) x)))
    (lambda (expected input)
      (assert
       (equal? expected
	       (pol->forward-list
		(make-persistent-ordered-list terrible-hash = input))))))
  '(() ())
  '((1) (1))
  '((1) (1 1))
  '((1 2) (1 2))
  '((2 1) (1 2 1))
  '((1 2) (1 2 1 2))
  '((3 1 2) (3 1 2))
  '((1 2 3) (3 1 2 3))
  '((1 2) (1 1 2))
  '((1 2) (1 2 2))
  '((1 2 3) (1 1 2 2 3 3)))

(define-test-group (pol->backward-list)
  (let ((terrible-hash (lambda (x) x)))
    (lambda (expected input)
      (assert
       (equal? expected
	       (pol->backward-list
		(make-persistent-ordered-list terrible-hash = input))))))
  '(() ())
  '((1) (1))
  '((1) (1 1))
  '((2 1) (1 2))
  '((1 2) (1 2 1))
  '((2 1) (1 2 1 2))
  '((2 1 3) (3 1 2))
  '((3 2 1) (3 1 2 3))
  '((2 1) (1 1 2))
  '((2 1) (1 2 2))
  '((3 2 1) (1 1 2 2 3 3)))

(define (pol/mutable pol)
  "Return a mutable copy of `pol'.  Changes to the copy will not affect `pol'."
  (let ((hamt (pol/hamt pol)))
    (if (hamt/mutable? hamt)
	pol
	(%make-persistent-ordered-list (pol/first pol)
				       (pol/last pol)
				       (hamt/mutable hamt)))))

(define (pol/immutable pol)
  "Return an immutable copy of `pol'.  Changes to `pol' will not affect the
copy."
  (let ((hamt (pol/hamt pol)))
    (if (hamt/mutable? pol)
	(%make-persistent-ordered-list (pol/first pol)
				       (pol/last pol)
				       (hamt/immutable hamt))
	pol)))

(define (pol-remove hamt datum)
  "Return `datum' from the `HAMT' of a POL.  Return three values, HAMT, X and Y.
HAMT is the updated `hamt'.  If the first element of the POL changed as a
result, X is the new first element; otherwise, it is #f.  If `datum' is removed,
Y is the element that was before it, if any; otherwise, it is #f."
  (let ((previous-next (hamt-fetch hamt datum)))
    (if (hamt-null? previous-next)
	(values hamt #f #f)
	(let* ((previous (car previous-next))
	       (next (cdr previous-next))
	       (previous* (and previous (pol/previous hamt previous)))
	       (next* (and next (pol/next hamt next)))
	       (hamt* (if previous
			  (hamt/put hamt previous (cons previous* next))
			  hamt)))
	  (values (if next
		      (hamt/put hamt* next (cons previous next*))
		      hamt*)
		  (and (not previous) next)
		  previous)))))

(define (pol/push pol datum)
  "Add `datum' to the end of `pol' without mutation, returning a new POL."
  (assert datum "No element may be #f.")
  (let* ((hamt (pol/hamt pol))
	 (last (pol/last pol)))
    (if (and last ((hamt/= hamt) datum last))
	pol
	(let-values (((hamt* first* previous*) (pol-remove hamt datum)))
	  (let ((hamt**
		 (if last
		     (hamt/put hamt
			       last
			       (cons (car (hamt-fetch hamt* last))
				     datum))
		     hamt*)))
	    (%make-persistent-ordered-list
	     (or first* (pol/first pol) datum)
	     datum
	     (hamt/put hamt** datum (cons last #f))))))))

(define-test-group (pol/push)
  (let ((terrible-hash (lambda (x) x)))
    (lambda (expected data)
      (let next ((data data)
		 (pol (make-persistent-ordered-list terrible-hash =)))
	(cond ((null? data)
	       (assert (equal? expected (pol->forward-list pol)))
	       (assert (equal? expected (reverse (pol->backward-list pol)))))
	      (else (next (cdr data) (pol/push pol (car data))))))))
  '(() ())
  '((1) (1))
  '((1) (1 1))
  '((1 2) (1 2))
  '((2 1) (1 2 1))
  '((1 2) (1 2 1 2))
  '((1 2) (1 2 1 1 2))
  '((1 2) (1 2 2)))

(define (pol/push! pol datum)
  "Destructively add `datum' to the end of `pol'."
  (assert datum "No element may be #f.")
  (let* ((hamt (pol/hamt pol))
	 (last (pol/last pol)))
    (if (and last ((hamt/= hamt) datum last))
	pol
	(let-values (((first* previous*) (pol-remove! hamt datum)))
	  (when last
	    (hamt/put! hamt last (cons (car (hamt-fetch hamt last)) datum)))
	  (hamt/put! hamt datum (cons last #f))
	  (set-pol/first! pol (or first* (pol/first pol) datum))
	  (set-pol/last! pol datum)
	  pol))))

(define-test-group (pol/push!)
  (let ((terrible-hash (lambda (x) x)))
    (lambda (expected data)
      (let ((pol (pol/mutable (make-persistent-ordered-list terrible-hash =))))
	(do-list (d data) (pol/push! pol d))
	(assert (equal? expected (pol->forward-list pol)))
	(assert (equal? expected (reverse (pol->backward-list pol)))))))
  '(() ())
  '((1) (1))
  '((1) (1 1))
  '((1 2) (1 2))
  '((2 1) (1 2 1))
  '((1 2) (1 2 1 2))
  '((1 2) (1 2 1 1 2))
  '((1 2) (1 2 2)))

(define (pol/pop pol)
  "Without mutating `pol', return both the last element in `pol' and `pol'
without that element.  Signal an error if `pol' is empty."
  (let ((hamt (pol/hamt pol))
	(last (pol/last pol)))
    (assert last "Persistent ordered list is empty." pol)
    (let ((previous (pol/previous hamt last))
	  (hamt* (hamt/put hamt last hamt-null)))
      (values last
	      (%make-persistent-ordered-list
	       (if previous (pol/first pol) #f)
	       previous
	       (if previous
		   (hamt/put hamt*
			     previous
			     (cons (pol/previous hamt previous) #f))
		   hamt*))))))

(define-test (pol/pop)
  (let* ((terrible-hash (lambda (x) x))
	 (pol (make-persistent-ordered-list terrible-hash = '(1 2))))
    (let-values (((datum pol*) (pol/pop pol)))
      (assert (= 2 datum))
      (assert (equal? '(1) (pol->forward-list pol*)))
      (assert (equal? '(1) (pol->backward-list pol*)))
      (let-values (((datum* pol**) (pol/pop pol*)))
	(assert (= 1 datum*))
	(assert (equal? '() (pol->forward-list pol**)))
	(assert (equal? '() (pol->backward-list pol**)))
	(assert (pol/empty? pol**))
	(assert-signals-condition condition-type:simple-error
				  (pol/pop pol**))))))

(define (pol/pop! pol)
  "Destructively remove the last element from `pol' and return it.  Signal an
error if `pol' is empty."
  (let ((hamt (pol/hamt pol))
	(last (pol/last pol)))
    (assert last "Persistent ordered list is empty." pol)
    (let ((previous (pol/previous hamt last)))
      (hamt/put! hamt last hamt-null)
      (when previous
	(let ((previous* (pol/previous hamt previous)))
	  (hamt/put! hamt previous (cons previous* #f))))
      (set-pol/last! pol previous)
      (unless previous (set-pol/first! pol #f)))
    last))

(define-test (pol/pop!)
  (let* ((terrible-hash (lambda (x) x))
	 (pol (pol/mutable
	       (make-persistent-ordered-list terrible-hash = '(1 2)))))
    (assert (= 2 (pol/pop! pol)))
    (assert (equal? '(1) (pol->forward-list pol)))
    (assert (equal? '(1) (pol->backward-list pol)))
    (assert (= 1 (pol/pop! pol)))
    (assert (equal? '() (pol->forward-list pol)))
    (assert (equal? '() (pol->backward-list pol)))
    (assert (pol/empty? pol))
    (assert-signals-condition condition-type:simple-error (pol/pop! pol))))