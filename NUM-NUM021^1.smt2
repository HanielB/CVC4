(set-option :incremental false)
(set-logic ALL)
(declare-sort $$unsorted 0)
(declare-fun zero ((-> $$unsorted $$unsorted) $$unsorted) $$unsorted)
(declare-fun one ((-> $$unsorted $$unsorted) $$unsorted) $$unsorted)
(declare-fun two ((-> $$unsorted $$unsorted) $$unsorted) $$unsorted)
(declare-fun three ((-> $$unsorted $$unsorted) $$unsorted) $$unsorted)
(declare-fun four ((-> $$unsorted $$unsorted) $$unsorted) $$unsorted)
(declare-fun five ((-> $$unsorted $$unsorted) $$unsorted) $$unsorted)
(declare-fun six ((-> $$unsorted $$unsorted) $$unsorted) $$unsorted)
(declare-fun seven ((-> $$unsorted $$unsorted) $$unsorted) $$unsorted)
(declare-fun eight ((-> $$unsorted $$unsorted) $$unsorted) $$unsorted)
(declare-fun nine ((-> $$unsorted $$unsorted) $$unsorted) $$unsorted)
(declare-fun ten ((-> $$unsorted $$unsorted) $$unsorted) $$unsorted)
(declare-fun succ ((-> (-> $$unsorted $$unsorted) $$unsorted $$unsorted) (-> $$unsorted $$unsorted) $$unsorted) $$unsorted)
(declare-fun plus ((-> (-> $$unsorted $$unsorted) $$unsorted $$unsorted) (-> (-> $$unsorted $$unsorted) $$unsorted $$unsorted) (-> $$unsorted $$unsorted) $$unsorted) $$unsorted)
(declare-fun mult ((-> (-> $$unsorted $$unsorted) $$unsorted $$unsorted) (-> (-> $$unsorted $$unsorted) $$unsorted $$unsorted) (-> $$unsorted $$unsorted) $$unsorted) $$unsorted)
(assert (= zero (lambda ((X (-> $$unsorted $$unsorted)) (Y $$unsorted)) Y)))
(assert (= one (lambda ((X (-> $$unsorted $$unsorted)) (Y $$unsorted)) (X Y))))
(assert (= two (lambda ((X (-> $$unsorted $$unsorted)) (Y $$unsorted)) (X (X Y)))))
(assert (= three (lambda ((X (-> $$unsorted $$unsorted)) (Y $$unsorted)) (X (X (X Y))))))
(assert (= four (lambda ((X (-> $$unsorted $$unsorted)) (Y $$unsorted)) (X (X (X (X Y)))))))
(assert (= five (lambda ((X (-> $$unsorted $$unsorted)) (Y $$unsorted)) (X (X (X (X (X Y))))))))
(assert (= six (lambda ((X (-> $$unsorted $$unsorted)) (Y $$unsorted)) (X (X (X (X (X (X Y)))))))))
(assert (= seven (lambda ((X (-> $$unsorted $$unsorted)) (Y $$unsorted)) (X (X (X (X (X (X (X Y))))))))))
(assert (= eight (lambda ((X (-> $$unsorted $$unsorted)) (Y $$unsorted)) (X (X (X (X (X (X (X (X Y)))))))))))
(assert (= nine (lambda ((X (-> $$unsorted $$unsorted)) (Y $$unsorted)) (X (X (X (X (X (X (X (X (X Y))))))))))))
(assert (= ten (lambda ((X (-> $$unsorted $$unsorted)) (Y $$unsorted)) (X (X (X (X (X (X (X (X (X (X Y)))))))))))))
(assert (= succ (lambda ((N (-> (-> $$unsorted $$unsorted) $$unsorted $$unsorted)) (X (-> $$unsorted $$unsorted)) (Y $$unsorted)) (X (N X Y)))))
(assert (= plus (lambda ((M (-> (-> $$unsorted $$unsorted) $$unsorted $$unsorted)) (N (-> (-> $$unsorted $$unsorted) $$unsorted $$unsorted)) (X (-> $$unsorted $$unsorted)) (Y $$unsorted)) (M X (N X Y)))))
(assert (= mult (lambda ((M (-> (-> $$unsorted $$unsorted) $$unsorted $$unsorted)) (N (-> (-> $$unsorted $$unsorted) $$unsorted $$unsorted)) (X (-> $$unsorted $$unsorted)) (Y $$unsorted)) (M (N X) Y))))
(assert (not (exists ((Op (-> (-> (-> $$unsorted $$unsorted) $$unsorted $$unsorted) (-> (-> $$unsorted $$unsorted) $$unsorted $$unsorted) (-> $$unsorted $$unsorted) $$unsorted $$unsorted))) (and (= (Op two three) five) (= (Op one two) three)) )))
(meta-info :filename "NUM021^1")
(check-sat-assuming ( (not false) ))
