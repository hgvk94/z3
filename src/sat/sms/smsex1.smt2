(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(declare-const e Bool)
(declare-const f Bool)

;; interpolant is (not (and (or c b) d (not a)))
(satmodsat (a b c d)
	   (and  (or (not f) (not e) a) (or f (not e) a) (or e (not a)) (or e (not b))
	         (or b (not c) (not d)))
	   (and (or d) (or a b c) (or (not a))))


;; interpolant is (not (and (or (not b) a) (or (not c) b (not d))))
(satmodsat (a b c d)
	   (and (or d) (or a b c) (or (not a)))
	   (and  (or (not f) (not e) a) (or f (not e) a) (or e (not a)) (or e (not b))
	         (or b (not c) (not d))))
