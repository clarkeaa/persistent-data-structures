;;; -*- Mode: LISP; -*-
;;;
;;; implentation of Driscoll's fat node persistent binary set from his
;;; paper "Making Data Structures Persistent."
;;;

(require 'lisp-unit)
(defpackage fat-persistent-binary-set
  (:use :common-lisp :lisp-unit)
  (:export :test))
(in-package fat-persistent-binary-set)

(defun cmp-number (x y)
  "The default compare function for numbers."
  (declare (type number x y))
  (the number (- x y)))

(defstruct version-tracker
  "The data structure for storing histories of version numbers."
  (vector (make-array 10 :fill-pointer 1 :adjustable t :initial-element -1)))

(defun version-tracker-add (vt parent)
  "This adds a new version to the version tracker VT who is a child of 
version PARENT and returns the integer representation of that new version."
  (declare (type version-tracker vt)
           (type integer parent))
  (with-slots (vector) vt
    (let ((new-version (length vector)))
      (vector-push parent vector)
      (the integer new-version))))

(defun version-tracker-get-parent (vt version)  
  "This returns the closest ancestor to VERSION in VT."
  (declare (type version-tracker vt)
           (type integer version))
  (with-slots (vector) vt
    (aref vector version)))

(defun version-tracker-max-version (vt)
  "This returns the maximum version number in VT."
  (declare (type version-tracker vt))
  (the integer (length (version-tracker-vector vt))))

(defun version-tracker-foreach (vt start func)
  "This executes FUNC across all ancestors of START in VT while FUNC keeps 
returning t."
  (declare (type version-tracker vt)
           (type integer start)
           (type function func))
  (when (and (>= start 0) (funcall func start))
    (version-tracker-foreach vt (version-tracker-get-parent vt start) func)))

(defun version-tracker-get-history (vt start)
  "Given VT this will return a list of all ancestors of START."
  (declare (type version-tracker vt)
           (type integer start))  
  (let ((answer (list)))
    (version-tracker-foreach vt
                             start
                             (lambda (version)
                               (setf answer (cons version answer))
                               t))
    answer))

(defun version-tracker-is-descendent (vt child parent)
  "This will decide if CHILD has as an ancestor PARENT in VT."
  (declare (type version-tracker vt)
           (type integer child parent))    
  (let ((answer))
    (version-tracker-foreach vt
                             child
                             (lambda (version)
                               (if (= version parent)
                                   (progn (setf answer t) nil)
                                   t)))
    answer))

(defstruct node
  "This is a fat binary tree node who has lists to versions of left nodes 
and right nodes."
  value
  (left-edges nil :type list)
  (right-edges nil :type list))

(defstruct edge
  "This is an edge between nodes that includes the version of the connection."
  (version 0 :type integer)
  node)

(defstruct entry
  "This is mutable shared data that exists across all versions of the SET."
  (version-tracker (make-version-tracker) :type version-tracker)
  (comparer #'cmp-number :type function)
  (edges (list (make-edge :version 0 :node nil)) :type list))

(defstruct set
  "This is the representation of a SET but at a specific VERSION."
  (version 0 :type integer)
  (entry (make-entry) :type entry))

(defmacro compare-cond ((comparer val1 val2) &key equals less greater)
  "This is a tertiary branch that runs COMPARER against VAL1 and VAL2
then branches into EQUALS LESS or GREATER based on the result."
  (let ((result (gensym)))
    `(let ((,result (funcall ,comparer ,val1 ,val2)))
       (cond ((< ,result 0) ,less)
             ((> ,result 0) ,greater)
             (t ,equals)))))

(defun entry-max-version (entry)
  "This returns the last version of ENTRY."
  (version-tracker-max-version (entry-version-tracker entry)))

(defun set-comparer (set)
  "This returns the comparer function of an ENTRY."
  (the function (entry-comparer (set-entry set))))

(defun set-update (set func)
  "This executes FUNC on the SET and updates SET's ENTRY to reflect
the new version created by FUNC.  FUNC should take in an INTEGER for
the version number we are creating and a NODE that represents where we
are starting the operation.  FUNC should then return the new NODE that
is the root for that version."
  (declare (type set set) (type function func))
  (let ((entry (set-entry set)))
    (with-slots ((entry-edges edges)) entry
      (let* ((max-version (entry-max-version entry))
             (op-version (set-version set))
             (version-tracker (entry-version-tracker entry))
             (new-version (version-tracker-add version-tracker op-version))
             ;; TODO make find-if binary search
             (start-edge (find-if (lambda (x) (= (edge-version x) op-version))
                                  entry-edges))
             (start-node (edge-node start-edge))
             (new-entry-node (funcall func new-version start-node))
             (new-entry-edge (make-edge :version new-version
                                        :node new-entry-node)))
        (setf entry-edges (cons new-entry-edge entry-edges))
        (setf max-version (1+ max-version))
        (make-set :version new-version
                  :entry entry)))))

(defun edges-apropos-node (edges version-tracker version)
  "This returns the most recent NODE from EDGES as decided by
referencing the current VERSION against the VERSION-TRACKER"
  (declare (type list edges)
           (type version-tracker version-tracker)
           (type integer version))
  ;; TODO make binary search instead
  (when (not (null edges))
    (let ((edge (car edges)))
      (if (and (<= (edge-version edge) version)
               (version-tracker-is-descendent version-tracker
                                              (edge-version edge)
                                              version))
          (the node (edge-node edge))
          (edges-apropos-node (cdr edges) version-tracker version)))))

(defun calc-node-left (node version-tracker version)
  "This returns most recent left child node from NODE as decided by 
referencing the current VERSION against the VERSION-TRACKER"
  (the node (edges-apropos-node (node-left-edges node)
                                version-tracker
                                version)))

(defun calc-node-right (node version-tracker version)
  "This returns most recent right child node from NODE as decided by 
referencing the current VERSION against the VERSION-TRACKER"
  (the node (edges-apropos-node (node-right-edges node)
                                version-tracker
                                version)))

(defmacro slot-update ((slot-name instance var-name) &body body)
  "Given a struct INSTANCE and a SLOT-NAME it will bind the value to
VAR-NAME then assign the value evaluated from BODY back to the slot."
  `(let ((,var-name (slot-value ,instance ,slot-name)))
     (setf (slot-value ,instance ,slot-name)
           ,@body)))

(defun set-add-child (&key node
                        calc-child-func
                        edges-slot-name
                        value
                        version
                        recurse-func)
  "This inserts a new child node onto NODE of VALUE and VERSION.  It
recurses into child determined by the CALC-CHILD-FUNC with the
RECURSE-FUNC if a leaf is not found.  When a new edge is created
EDGES-SLOT-NAME is used to update the NODE's slot.  It always returns
NODE."
  (let ((child (funcall calc-child-func node)))
    (if (null child)
        (let* ((new-node (make-node :value value))
               (new-edge (make-edge :version version :node new-node)))
          (slot-update (edges-slot-name node x) (cons new-edge x)))
        (funcall recurse-func version child))
    node))

(defun set-add (set val)
  "This inserts VAL into SET and returns a new instance of SET with
the version reflecting this edit."
  (declare (optimize (safety 3) (debug 3)))
  (let ((comparer (set-comparer set))
        (version-tracker (entry-version-tracker (set-entry set)))
        (op-version (set-version set)))
    (labels ((calc-recent-left-child (node)
               (calc-node-left node version-tracker op-version))
             (calc-recent-right-child (node)
               (calc-node-right node version-tracker op-version))
             (add (new-version node)
               (if (null node)
                   (make-node :value val)
                   (compare-cond
                    (comparer val (node-value node))
                    :equals
                    node
                    :less
                    (set-add-child :node node
                                   :calc-child-func #'calc-recent-left-child
                                   :edges-slot-name 'left-edges
                                   :value val
                                   :version new-version
                                   :recurse-func #'add)
                    :greater
                    (set-add-child :node node
                                   :calc-child-func #'calc-recent-right-child
                                   :edges-slot-name 'right-edges
                                   :value val
                                   :version new-version
                                   :recurse-func #'add)))))
      (set-update set #'add))))

(defun set-depth-first (set func)
  "This runs FUNC across all values in SET in a depth first order."
  (let* ((version (set-version set))
         (entry (set-entry set))
         (version-tracker (entry-version-tracker entry))
         (entry-edges (entry-edges entry))
         (start-edge (find-if (lambda (x) (= (edge-version x) version))
                              entry-edges)))
    (labels ((recurse (node)
               (when (not (null node))
                 (recurse (calc-node-left node version-tracker version))
                 (recurse (calc-node-right node version-tracker version))
                 (funcall func (node-value node)))))
      (recurse (edge-node start-edge))
      t)))

(defun set->list (set)
  "This converts a SET into a LIST."
  (let ((elements nil))
    (set-depth-first set (lambda (x) (setq elements (cons x elements))))
    elements))

(defun test ()
  (setq *print-failures* t)
  (run-tests :all :fat-persistent-binary-set))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;tests;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defpackage fat-persistent-binary-set-test
;;   (:use :common-lisp :fat-persistent-binary-set :lisp-unit))
;; (in-package fat-persistent-binary-set-test)

(define-test test-make
  (let* ((set (make-set))
         (elements (set->list set)))
    (assert-equal elements nil)))

(define-test test-add-one
  (let* ((set1 (make-set))
         (set2 (set-add set1 1234))
         (elements1 (set->list set1))
         (elements2 (set->list set2)))
    (assert-equal elements1 nil)
    (assert-true (find 1234 elements2))
    (assert-equal 1 (length elements2))))

(define-test test-add-two
  (let* ((set1 (make-set))
         (set2 (set-add set1 1234))
         (set3 (set-add set2 5678))
         (elements1 (set->list set1))
         (elements2 (set->list set2))
         (elements3 (set->list set3)))
    (assert-equal elements1 nil)
    (assert-true (find 1234 elements2))
    (assert-equal 1 (length elements2))
    (assert-true (find 1234 elements3))
    (assert-true (find 5678 elements3))
    (assert-equal 2 (length elements3))))

(define-test test-split-history
  (let* ((set1 (make-set))
         (set2 (set-add set1 1))
         (set3 (set-add set2 2))
         (set4 (set-add set2 3))
         (elements3 (set->list set3))
         (elements4 (set->list set4)))
    (assert-true (find 1 elements3))
    (assert-true (find 2 elements3))
    (assert-equal 2 (length elements3))
    (assert-true (find 1 elements4))
    (assert-true (find 3 elements4))
    (assert-equal 2 (length elements4))))

(define-test test-version-tracker-1
  (let* ((vt (make-version-tracker))
         (new-version (version-tracker-add vt 0)))
    (assert-equal 1 new-version)
    (assert-equal (version-tracker-get-parent vt new-version) 0)))

(define-test test-version-tracker-version
  (let* ((vt (make-version-tracker)))
    (assert-equal 1 (version-tracker-max-version vt))
    (version-tracker-add vt 0)
    (assert-equal 2 (version-tracker-max-version vt))
    (version-tracker-add vt 0)
    (assert-equal 3 (version-tracker-max-version vt))))

(define-test test-version-tracker-2
  (let* ((vt (make-version-tracker))
         (v1 (version-tracker-add vt 0))
         (v2 (version-tracker-add vt 0))
         (v1-history (version-tracker-get-history vt v1))
         (v2-history (version-tracker-get-history vt v2)))
    (assert-equal 1 v1)
    (assert-equal 2 v2)
    (assert-true (find 0 v1-history))
    (assert-true (find 1 v1-history))
    (assert-equal 2 (length v1-history))
    (assert-true (find 0 v2-history))
    (assert-true (find 2 v2-history))
    (assert-equal 2 (length v2-history))))

(define-test test-is-descendent
  (let* ((vt (make-version-tracker))
         (v1 (version-tracker-add vt 0))
         (v2 (version-tracker-add vt v1))
         (v3 (version-tracker-add vt v1)))
    (assert-true (version-tracker-is-descendent vt v3 v1))
    (assert-true (version-tracker-is-descendent vt v2 v1))
    (assert-false (version-tracker-is-descendent vt v2 v3))
    (assert-false (version-tracker-is-descendent vt v3 v2))))
