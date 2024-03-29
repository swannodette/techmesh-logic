(ns techmesh-logic.core
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :as l])
  (:require [clojure.core.logic.fd :as fd]
            [clojure.tools.macro :as m]
            [clojure.pprint :as pp]))

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

(doall
  (run* [q]
    (fn [a]
      (println a)
      a)))

(doall
  (run* [q]
    (fresh [x y]
      (== x 1)
      (== y 2)
      (== q [x y])
      (fn [a]
        (println a)
        a))))

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

(time
  (dotimes [_ 1000]
    (doall
      (run-nc 1 [q]
        (zebrao q)))))

;; -----------------------------------------------------------------------------
;; Map unification

(run* [q]
  (== {:foo q} {:foo 'bar}))

(run* [q]
  (== {:foo q} {:foo 'bar :baz 'woz}))

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
    (fd/in x y z (fd/interval 0 9))
    (== x 1)
    (== y 2)
    (fd/+ x y z)
    (== q [x y z])))

(run* [q]
  (fresh [x y z]
    (== q [x y z])
    (fd/+ x y z)
    (== x 1)
    (== y 2)
    (fd/in x y z (fd/interval 0 9))))

(run* [q]
  (fresh [x y]
    (== q [x y])
    (fd/in x y (fd/interval 0 9))
    (fd/+ x y 9)
    (fresh [p0 p1]
      (fd/in p0 p1 (fd/interval 0 99))
      (fd/* 2 x p0)
      (fd/* 4 y p1)
      (fd/+ p0 p1 24))))

(run* [q]
  (fresh [x y]
    (fd/in x y (fd/interval 0 9))
    (fd/eq
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

(pp/pprint (->rows data))

(defn ->cols [rows]
  (apply map vector rows))

(pp/pprint (->cols (->rows data)))

(defn get-square [rows x y]
  (for [x (range x (+ x 3))
        y (range y (+ y 3))]
    (get-in rows [x y])))

(pp/pprint (get-square (->rows data) 0 0))

(defn ->squares [rows]
  (for [x (range 0 9 3)
        y (range 0 9 3)]
    (get-square rows x y)))

(pp/pprint (->squares (->rows data)))

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
      (everyg #(fd/in % (fd/domain 1 2 3 4 5 6 7 8 9)) vars)
      (init vars hints)
      (everyg fd/distinct rows)
      (everyg fd/distinct cols)
      (everyg fd/distinct sqs))))

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

(time
  (dotimes [_ 100]
    (doall (sudokufd data))))
