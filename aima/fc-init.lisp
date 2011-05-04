(defun fc-init ()
  "Load aima codebase and forward chaining implementation."
  (load "aima/aima.lisp")
  (aima-load 'logic)
  (load "aima/logic/algorithms/fc.lisp"))