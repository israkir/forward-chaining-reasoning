;;; -*- Mode: Lisp; Syntax: Common-Lisp; -*- File: logic/fc.lisp

;;;; Forward-Chaining Algorithm Implementation

;;; Author	: B96902133, Hakki Caner Kirmizi
;;; Usage	: 
;;; ---------
;;; $ (load "aima/fc-init.lisp")
;;; $ (fc-init)
;;;	$ (test 'criminal-kb)
;;;	$ (test 'family-kb)
;;; $ (test 'lecture-kb)


;;;; Test knowledge bases

(deftest criminal-kb
  "Construct and test a sample forward chaining knowledge base:
  Criminal' problem from [p 271-272] in AIMA."
  ((setf criminal-kb (make-horn-kb)))
  ((tell criminal-kb "American(x) ^ Weapon(y) ^ Nation(z) ^ Hostile(z) ^ Sells(x,z,y)
		 => Criminal(x)"))
  ((tell criminal-kb "Owns(Nono,M1)"))
  ((tell criminal-kb "Missle(M1)"))
  ((tell criminal-kb "Owns(Nono,x) ^ Missle(x) => Sells(West,Nono,x)"))
  ((tell criminal-kb "Missle(x) => Weapon(x)"))
  ((tell criminal-kb "Enemy(x,America) => Hostile(x)"))
  ((tell criminal-kb "American(West)"))
  ((tell criminal-kb "Nation(Nono)"))
  ((tell criminal-kb "Enemy(Nono,America)"))
  ((tell criminal-kb "Nation(America)"))
  ;; Query and test sample knowledge base
  ((ask-fc-pattern criminal-kb "Missle(x)"))
  ((ask-fc criminal-kb "Enemy(America,Nono)"))
  ((ask-fc criminal-kb "Enemy(Nono,America)"))
  ((ask-fc criminal-kb "Missle(West)"))
  ((ask-fc criminal-kb "Criminal(West)"))
  ((ask-fc criminal-kb "Enemy(Nono,West)"))
  ((ask-fc-pattern criminal-kb "Criminal(x)"))
  ((ask-fc-pattern criminal-kb "Hostile(x)"))
  ((ask-fc-pattern criminal-kb "Weapon(x)"))
  ((ask-fc-pattern criminal-kb "Nation(x)")))
  
(deftest family-kb
  "Construct and test a sample forward chaining knowledge 
  base about family relations."
  ((setf family-kb (make-horn-kb)))
  ((tell family-kb "Mother(Gerda,Peter)"))
  ((tell family-kb "Father(Torsten,Peter)"))
  ((tell family-kb "Father(Peter,Isabella)"))
  ((tell family-kb "Father(Peter,Juliet)"))
  ((tell family-kb "Mother(x,y) => Parent(x,y)"))
  ((tell family-kb "Father(x,y) => Parent(x,y)"))
  ((tell family-kb "Parent(g,p) ^ Parent(p,c) => Grandparent(g,c)"))
  ((ask-fc family-kb "Parent(Gerda,Peter)"))
  ((ask-fc-pattern family-kb "Parent(Peter,x)"))
  ((ask-fc-pattern family-kb "Parent(x,Peter)"))
  ((ask-fc-pattern family-kb "Grandparent(x,z)")))
  
(deftest lecture-kb
    "Construct another test knowledge base.
    Based on Yannick Pencole's class example in here:
    http://homepages.laas.fr/ypencole/KRR3.pdf"
    ((setf lecture-kb (make-horn-kb)))
    ;; 'A person who gives good lectures about AI to her students enjoying the lectures is a good teacher.'
    ((tell lecture-kb "Person(x) ^ GoodAILectures(y) ^ Students(z) ^ Gives(x,y,z) ^ Enjoys(z,y) => GoodTeacher(x)"))
    ;; 'This group of people have good logic lectures.'
    ((tell lecture-kb "Have(People,x) ^ GoodLogicLectures(x)"))
    ;; 'If this group of people have good AI lectures, then they enjoy the lectures.'
    ((tell lecture-kb "Have(People,x) ^ GoodAILectures(x) => Enjoys(People,x)"))
    ;; 'All of the logic lectures of this group of people are given by Jane.'
    ((tell lecture-kb "GoodLogicLectures(x) ^ Have(People,x) => Gives(Jane,x,People)"))
    ;; 'This group of people are studying at NTU.'
    ((tell lecture-kb "Study(People,NTU)"))
    ;; 'Jane is a person.'
    ((tell lecture-kb "Person(Jane)"))
    ;; 'John is a person.'
    ((tell lecture-kb "Person(John)"))
    ;; 'Whom that study in NTU are students.'
    ((tell lecture-kb "Study(x,NTU) => Students(x)"))
    ;; If the logic lectures are good, so are the AI lectures.'
    ((tell lecture-kb "GoodLogicLectures(x) => GoodAILectures(x)"))
    ;; '? Ask whether Jane is a good teacher or not.'
    ((ask-fc lecture-kb "GoodTeacher(Jane)"))
    ;; '? Ask who is the good teacher.'
    ((ask-fc-pattern lecture-kb "GoodTeacher(x)")))


;;;; Algorithm implementation
  
(defmethod ask-fc-each ((kb horn-kb) query fn)
  "Use forward chaining to decide if the sentence is true."
  (forward-chain-each kb (->cnf query) +no-bindings+ fn))
  
(defun ask-fc (kb query)
  "Ask if query sentence is true using forward chaining; return t or nil."
  (ask-fc-each kb (logic query)
            #'(lambda (s) (declare (ignore s)) (RETURN-FROM ASK-FC t))))

(defun ask-fc-pattern (kb query &optional (pattern query))
  "Ask if query sentence is true; if it is, substitute bindings into pattern."
  (setq substitutions ())
  (ask-each kb (logic query)
            #'(lambda (s) (push (subst-bindings s (logic pattern)) substitutions)))
  (setq results nil)
  (for each substitution in substitutions do
    (setf already-in nil)
    (for each elem in results do
      (if (equal elem substitution) (setf already-in t)))
    (if (not already-in) (push substitution results)))
  (reverse results))
                            
(defun forward-chain-each (kb goal bindings fn)
  "Forward chain with given knowledge base and query."
  (setq new +no-bindings+)
  (loop while (not (equal new ())) do
	(setq new ())
	(loop for value being the hash-value of (horn-kb-table kb) do 
	  (for each sentence in value do
		(setq new-sentence (rename-variables sentence))
		;; extract premises in the rule: p1 ^ p2 ^ ... ^ pn
		(setq premises (conjuncts (->cnf (arg1 new-sentence))))
		;; extract conclusion in the rule: q
		(setq conclusion (arg2 new-sentence))
		;; calc for each subst theta s.t. for each possible binding in kb
		(setf possible-bindings (find-possible-bindings kb premises bindings fn))
        (loop for binding in possible-bindings do
		  (setq result (subst-bindings binding conclusion))
		  ;; test result is a renaming of some sentence in kb already
		  (setf already-in-kb nil)
		  (loop for clause in (gethash (op result) (horn-kb-table kb)) do
			(setq new-clause (rename-variables clause))
			(cond ((equal (arg1 new-clause) 'TRUE)
			  (cond ((null already-in-kb)
				(setf already-in-kb (renaming? result (arg2 new-clause))))))))
		  ;; test result is a renaming of some sentence in new already
		  (setf already-in-new nil)
		  (loop for fact in new do
            (cond ((null already-in-new)
			  (setf already-in-new (renaming? result fact)))))
          (cond ((and (null already-in-kb) (null already-in-new))
		    (setf new (append (list result) new))))
		  (setf unifier (unify result goal))
		  (cond ((null unifier))
            (t (funcall fn unifier))))))
    (for each fact in new do
	  (tell kb fact))))

(defun find-possible-bindings (kb premises bindings fn)
  "Recursively get all possible bindings in kb; based on TA's power-assignment."
  (cond ((null premises) (list bindings))
	(t (let ((first-of-premises (first premises)) 
	      (rest-of-premises (rest premises)) 
		  (result '()))
      (for each clause in (gethash (op first-of-premises) (horn-kb-table kb)) do
	    (let ((new-clause (rename-variables clause)))
	      (cond ((equal (arg1 new-clause) 'TRUE)
	        (setq result 
			  (append 
			    (find-possible-bindings kb rest-of-premises (unify first-of-premises (arg2 new-clause) bindings) fn) 
				  result))))))
    result))))