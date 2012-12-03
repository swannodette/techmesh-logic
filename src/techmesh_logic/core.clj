(ns techmesh-logic.core
  (:refer-clojure :exclude [==])
  (:require [clojure.tools.macro :as m]
            [clojure.pprint :as pp])
  (:use [clojure.core.logic :as l]))

;; -----------------------------------------------------------------------------
;; Basics

; Q=true.

(run* [q]
  (== q true))

; true=Q.

(run* [q]
  (== true q))

; Q=false.

(run* [q]
  (== q false))

; Q=true, Q=false.

(run* [q]
  (== q true)
  (== q false))

; Q=X, X=1.

(run* [q]
  (fresh [x]
    (== q x)
    (== x 1)))

; Q=[X,Y].

(run* [q]
  (fresh [x y]
    (== q [x y])))

; no translation

(run* [q]
  (let [local (+ 1 2)]
    (fresh []
      (== q local))))

; [X,2]=[1,Y], Q=[X,Y].

(run* [q]
  (fresh [x y]
    (== [x 2] [1 y])
    (== q [x y])))

;; -----------------------------------------------------------------------------
;; Under the hood

;; we can get at the machinery, just closures

(run* [q]
  (fn [a]
    (println a)
    a))

(run* [q]
  (fresh [x y]
    (== x 1)
    (== y 2)
    (== q [x y])
    (fn [a]
      (println a)
      a)))

;; -----------------------------------------------------------------------------
;; Disjunction

; Q=tea; Q=coffee.

(run* [q]
  (conde
    [(== q 'tea)]
    [(== q 'coffee)]))

(run 1 [q]
  (conde
    [(== q 'tea)]
    [(== q 'coffee)]))

;; -----------------------------------------------------------------------------
;; Fair disjunction

; no translation

(defn nevero []
  (fresh []
    (nevero)))

(run* [q]
  (conde
    [(nevero)]
    [(== q 'tea)]))

(run 1 [q]
  (conde
    [(nevero)]
    [(== q 'tea)]))

;; -----------------------------------------------------------------------------
;; Some relations

(cons 'a '(b c))

; [a|[b,c]]=Q.

(run* [q]
  (conso 'a '(b c) q))

; [Q|[b,c]]=[a,b,c].

(run* [q]
  (conso q '(b c) '(a b c)))

; [a|Q]=[a,b,c].

(run* [q]
  (conso 'a q '(a b c)))

; [b|Q]=[a,b,c].

(run* [q]
  (conso 'b q '(a b c)))

; [X|[b,c]]=Q.

(run* [q]
  (fresh [x]
    (conso x '(b c) q)))

;; -----------------------------------------------------------------------------
;; A little sugar a la PROLOG

; sugar([H|T],[head-H,tail-T]).

(defne sugar [l o]
  ([[h . t] [:head h :tail t]]))

; sugar([cat,bird,dog],Q).

(run* [q]
  (sugar '(cat bird dog) q))

;; /////////////////////////////////////////////////////////////////////////////
;; SLIDES
;; /////////////////////////////////////////////////////////////////////////////

;; -----------------------------------------------------------------------------
;; Zebra

(defne righto [x y l]
  ([_ _ [x y . r]])
  ([_ _ [_ . r]] (righto x y r)))

(run* [q]
  (righto 'dog 'cat '(dog bird cat)))

(run* [q]
  (righto 'dog 'cat '(dog cat bird)))

(run* [q]
  (righto 'dog 'cat '(cat dog bird)))

(defn nexto [x y l]
  (conde
    [(righto x y l)]
    [(righto y x l)]))

(run* [q]
  (nexto 'dog 'cat '(cat dog bird)))

(defn zebrao [hs]
  (m/symbol-macrolet [_ (lvar)]
    (fresh []
     (== [_ _ [_ _ 'milk _ _] _ _] hs)
     (firsto hs ['norwegian _ _ _ _])
     (nexto ['norwegian _ _ _ _] [_ _ _ _ 'blue] hs)
     (righto [_ _ _ _ 'ivory] [_ _ _ _ 'green] hs)
     (membero ['englishman _ _ _ 'red] hs)
     (membero [_ 'kools _ _ 'yellow] hs)
     (membero ['spaniard _ _ 'dog _] hs)
     (membero [_ _ 'coffee _ 'green] hs)
     (membero ['ukrainian _ 'tea _ _] hs)
     (membero [_ 'lucky-strikes 'oj _ _] hs)
     (membero ['japanese 'parliaments _ _ _] hs)
     (membero [_ 'oldgolds _ 'snails _] hs)
     (nexto [_ _ _ 'horse _] [_ 'kools _ _ _] hs)
     (nexto [_ _ _ 'fox _] [_ 'chesterfields _ _ _] hs))))

(pp/pprint
 (run 1 [q]
   (zebrao q)))

(dotimes [_ 5]
  (time
    (dotimes [_ 1000]
      (run-nc 1 [q]
        (zebrao q)))))

;; -----------------------------------------------------------------------------
;; Map unification

(run* [q]
  (== {:foo q} {:foo 'bar}))

(run* [q]
  (== {:foo q} {:foo 'bar :baz 'woz}))

;; -----------------------------------------------------------------------------
;; Extensible unification (see Equality for Prolog)

(defprotocol IUnifyWithFoo
  (unify-with-foo [v u s]))

(deftype Foo []
  IUnifyTerms
  (unify-terms [u v s]
    (unify-with-foo v u s))
  IUnifyWithFoo
  (unify-with-foo [v u s]
    (when (instance? Foo v)
      s)))

(extend-protocol IUnifyWithFoo
  nil
  (unify-with-foo [v u s] nil)

  Object
  (unify-with-foo [v u s] nil))

(run* [q]
  (== (Foo.) 1))

(run* [q]
  (== (Foo.) 'techmesh-rocks!))

(run* [q]
  (== (Foo.) (Foo.)))

(run* [q]
  (== (partial-map {:foo 'bar}) {:foo 'bar :baz 'woz}))

(run* [q]
  (== (partial-map {:foo 'bar}) {:baz 'woz}))

;; -----------------------------------------------------------------------------
;; Disequality

(run* [q]
  (fresh [x y]
    (!= x y)
    (== q [x y])))

(run* [q]
  (fresh [x y]
    (!= [x 2] [1 y])
    (== x 1)
    (== q [x y])))

(run* [q]
  (fresh [x y]
    (!= [x 2] [1 y])
    (== y 2)
    (== q [x y])))

(run* [q]
  (fresh [x y]
    (!= [x 2] [1 y])
    (== x 1) (== y 2)
    (== q [x y])))

;; -----------------------------------------------------------------------------
;; Projection

; X=1, Y=2, Z=X+Y, Q=[X,Y,Z].

(run* [q]
  (fresh [x y z]
    (== x 1)
    (== y 2)
    (== z (+ x y))
    (== q [x y z])))

; X=1, Y=2, Z is X+Y, Q=[X,Y,Z].

(run* [q]
  (fresh [x y z]
    (== x 1)
    (== y 2)
    (project [x y]
      (== z (+ x y)))
    (== q [x y z])))

; Z is X+Y, X=1, Y=2, Q=[X,Y,Z].

(run* [q]
  (fresh [x y z]
    (project [x y]
      (== z (+ x y)))
    (== x 1)
    (== y 2)
    (== q [x y z])))

;; /////////////////////////////////////////////////////////////////////////////
;; SLIDES
;; /////////////////////////////////////////////////////////////////////////////

;; -----------------------------------------------------------------------------
;; Finite Domains

(run* [q]
  (fresh [x y z]
    (infd x y z (interval 0 9))
    (== x 1)
    (== y 2)
    (+fd x y z)
    (== q [x y z])))

(run* [q]
  (fresh [x y z]
    (== q [x y z])
    (+fd x y z)
    (== x 1)
    (== y 2)
    (infd x y z (interval 0 9))))

(run* [q]
  (fresh [x y]
    (== q [x y])
    (infd x y (interval 0 9))
    (+fd x y 9)
    (fresh [p0 p1]
      (infd p0 p1 (interval 0 99))
      (*fd 2 x p0)
      (*fd 4 y p1)
      (+fd p0 p1 24))))

(run* [q]
  (fresh [x y]
    (infd x y (interval 0 9))
    (eqfd
      (= (+ x y) 9)
      (= (+ (* x 2) (* y 4)) 24))
    (== q [x y])))

;; -----------------------------------------------------------------------------
;; Sudoku

(def data
  [0 0 3  0 2 0  6 0 0
   9 0 0  3 0 5  0 0 1
   0 0 1  8 0 6  4 0 0

   0 0 8  1 0 2  9 0 0
   7 0 0  0 0 0  0 0 8
   0 0 6  7 0 8  2 0 0

   0 0 2  6 0 9  5 0 0
   8 0 0  2 0 3  0 0 9
   0 0 5  0 1 0  3 0 0])

(defn ->rows [xs]
  (->> xs (partition 9) (map vec) (into [])))

(->rows data)

(defn ->cols [rows]
  (apply map vector rows))

(->cols (->rows data))

(defn get-square [rows x y]
  (for [x (range x (+ x 3))
        y (range y (+ y 3))]
    (get-in rows [x y])))

(get-square (->rows data) 0 0)

(defn ->squares [rows]
  (for [x (range 0 9 3)
        y (range 0 9 3)]
    (get-square rows x y)))

(->squares (->rows data))

(defn init [vars hints]
  (if (seq vars)
    (let [hint (first hints)]
      (all
       (if-not (zero? hint)
         (== (first vars) hint)
         succeed)
       (init (next vars) (next hints))))
    succeed))

(defn sudokufd [hints]
  (let [vars (repeatedly 81 lvar) 
        rows (->rows vars)
        cols (->cols rows)
        sqs  (->squares rows)]
    (run-nc 1 [q]
      (== q vars)
      (everyg #(infd % (domain 1 2 3 4 5 6 7 8 9)) vars)
      (init vars hints)
      (everyg distinctfd rows)
      (everyg distinctfd cols)
      (everyg distinctfd sqs))))

(sudokufd data)

(defn print-solution [vars]
  (println)
  (doseq [row-group (->> vars
                        (partition 9)
                        (partition 3)
                        (interpose "\n\n"))]
    (if-not (string? row-group)
      (doseq [row (interpose "\n" row-group)]
        (if-not (string? row)
          (doseq [x (->> row
                         (partition 3)
                         (map #(interpose " " %))
                         (interpose "  "))]
            (print (apply str x)))
          (print row)))
      (print row-group)))
  (println))

(print-solution (first (sudokufd data)))

(defn verify [vars]
  (let [rows (->rows vars)
        cols (->cols rows)
        sqs  (->squares rows)
        verify-group (fn [group]
                       (every? #(= (->> % (into #{}) count) 9)
                          group))]
    (and (verify-group rows)
         (verify-group cols)
         (verify-group sqs))))

(verify (first (sudokufd data)))

(dotimes [_ 5]
  (time
    (dotimes [_ 100]
      (sudokufd data))))

;; -----------------------------------------------------------------------------
;; Extensible Constraints

(defc numberc [x]
  (number? x))

(run* [q]
  (numberc q))

(run* [q]
  (fresh [x]
    (numberc x)
    (== q [x :foo])
    (== q [1 :foo])))

(run* [q]
  (fresh [x]
    (numberc x)
    (== q [x :foo])
    (== q ["foo" :foo])))

;; -----------------------------------------------------------------------------
;; Under the hood

(defn -not-pathc
  ([x path] (-not-pathc x path nil))
  ([x path id]
     (reify
       clojure.lang.IFn
       (invoke [this a]
         (let [x (walk a x)]
           (if (not (map? x))
             ((remcg this) a)
             (when (= (get-in x path ::not-found) ::not-found)
               ((remcg this) a)))))
       IConstraintOp
       (rator [_] `pathc)
       (rands [_] [x path])
       IWithConstraintId
       (with-id [_ id]
         (-not-pathc x path id))
       IRunnable
       (runnable? [_ s]
         (not (lvar? (walk s x))))
       IRelevant
       (-relevant? [_ s] true)
       IConstraintWatchedStores
       (watched-stores [_] #{:clojure.core.logic/subst}))))

(rator (-not-pathc {:foo 'bar} '[baz woz]))

(rands (-not-pathc {:foo 'bar} '[baz woz]))

(runnable? (-not-pathc {:foo 'bar} '[baz woz]) empty-s)

(defn not-pathc [x path]
  (cgoal (-not-pathc x path)))

(run* [q]
  (not-pathc q [:a :b])
  (== q 1))

(run* [q]
  (not-pathc q [:a :b])
  (== q {:a 2}))

(run* [q]
  (not-pathc q [:a :b])
  (== q {:a {:c 2}}))

(run* [q]
  (not-pathc q [:a :b])
  (== q {:a {:b 1}}))
