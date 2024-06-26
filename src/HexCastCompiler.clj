(ns HexCastCompiler
  (:require
   [clojure.core.match :refer [match]]
   [crypticbutter.snoop :refer [>defn]]
   [malli.core :as m]
   [malli.instrument :as mi]))

(def Name [:or :keyword :symbol])
(def Term
  [:multi {:dispatch first}
     Name
     [:= [:tuple [:= :=] Name]]
     [:var [:tuple [:= :var] :keyword]]])
(def Vars [:sequential [:map [:index :int] [:name :keyword]]])
(def FnContext
  "Returns the effect of an action on the stack, as the number of iotas pushed minus the number popped"
  [:function [:cat Name] :int])

(>defn var-index [vars name]
  [Vars :keyword :=> [:maybe pos-int?]]
  (loop [vars (seq vars)]
    (when vars
      (if (= (:name (first vars)) name)
        (:index (first vars))
        (recur (next vars))))))

(>defn shift-vars
  ([vars shift-by]
   [Vars :int :=> Vars]
   (map #(update % :index + shift-by) vars))
  ([vars]
   [Vars := Vars]
   (shift-vars vars 1)))

(>defn unvar
  "Leaves unrecognized variables unexpanded."
  ([terms signature-of] (unvar [] terms signature-of))
  ([vars terms signature-of]
   [[Vars] [:sequential Term] FnContext :=> [:sequential Term]]
   (match (seq terms)
     nil []
     ([[:= name] & more] :seq)
     (recur (conj vars {:index 0, :name name}) more signature-of)
     ([[:var (name :guard #(var-index vars %))] & more] :seq)
     (lazy-seq (concat [(var-index vars name) :fishermans-gambit-2]
                       (unvar (shift-vars vars) more signature-of)))
     ([pattern & more] :seq)
     (do
       (assert (signature-of pattern))
       (lazy-seq (cons pattern (unvar (shift-vars vars (signature-of pattern))
                                      more
                                      signature-of)))))))

(>defn qquote-vars*
  "Requires the top of the stack to be a list, which the result of the function will be appended onto.
  Leaves unrecognized variables unexpanded."
  ([vars terms]
   [Vars [:sequential Term] :=> [:sequential Term]]
   (when (seq terms)
     (let [parse-terms [:altn [:quote [:cat [:+ Name] [:* :any]]]
                              [:unquote [:cat [:tuple [:= :var] Name] [:* :any]]]]]
       (match (m/parse parse-terms terms)
         [:quote [symbols more]]
         (lazy-seq (concat [:introspection] symbols [:retrospection :combination-distillation]
                           (qquote-vars* vars more)))
         [:unquote [[:var (name :guard #(var-index vars %))] more]]
         (lazy-seq (concat [(var-index vars name) :fishermans-gambit-2 :singles-purification :combination-distillation]
                           (qquote-vars* vars more)))
         [:unquote [[:var name] more]]
         (lazy-seq (cons [:var name] (qquote-vars* vars more))))))))

(defn qquote-vars [vars terms]
  (cons :vacant-reflection
        (qquote-vars* (shift-vars vars) terms)))

(def std-signatures (constantly 1))

(def hex-loop
  (let [compile-args [{:name `init, :index 3}
                      {:name `pred, :index 2}
                      {:name `body, :index 1}
                      {:name `update, :index 0}]
        runtime-args [{:name `self, :index 1}
                      {:name `i, :index 0}]
        signatures `{init 1, `pred 0, `body -1, `update 0}
        decider (qquote-vars compile-args `[[:var i] [:var pred]])
        if-branch (qquote-vars compile-args `[[:var i] [:var body] [:var self] [:var i] [:var update] [:var self] :hermes-gambit])
        else-branch [:vacant-reflection]
        loop-code (unvar runtime-args
                         (concat decider if-branch else-branch [:augurs-gambit :hermes-gambit])
                         (some-fn signatures std-signatures))]
    (concat decider if-branch else-branch [:augurs-gambit :hermes-gambit])))

(mi/instrument!)
