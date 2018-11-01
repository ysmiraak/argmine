(ns user)

(defn check [expr env]
  (cond (find env expr) (list env)
        (symbol? expr)  (list (assoc env expr true) (assoc env expr false))
        :else (let [[x op y] expr]
                (for [env (check x env)
                      env (check y env)]
                  (assoc env expr
                         (condp = op
                           '-> (or (not (env x)) (env y))
                           '* (and (env x) (env y))
                           '+ (or (env x) (env y))))))))

;; anything which not attacted or derived are facts (leaf nodes)

(defn lift [x] (fn [f] (f x)))

(defn valid? [expr claim facts]
  (as-> facts $
    (zipmap $ (repeat true))
    (assoc $ 0 false 1 true)
    (check expr $)
    (filter (lift expr) $)
    (mapcat (partial check claim) $)
    (some->> $ seq (every? (lift claim)))))

(defmacro valid! [expr claim facts]
  `(valid? '~expr '~claim '~facts))

(comment

  support => true
  (valid! (p -> q) q [p])

  serial support => true
  (valid! ((p -> q) * (q -> r)) r [p])

  linked support => true
  (valid! ((p * q) -> r) r [p q])
  (valid! (q -> (p -> r)) r [p q])

  multiple support => true
  (valid! ((p + q) -> r) r [p q])

  counter => false
  (valid! (r -> (q -> 0)) q [r])

  counter and support => nil
  ;; q is good because p,
  ;; q is bad because r,
  ;; therefore q
  (valid! ((p -> q) * (r -> (q -> 0))) q [p r])

  rebut rebutter => false
  (valid! ((r -> (q -> 0)) * (s -> (r -> 0))) q [s])

  support and rebut rebutter => true
  (valid! ((p -> q) * ((r -> (q -> 0)) * (s -> (r -> 0)))) q [p s])

  undercut => false
  (valid! (r -> ((p -> q) -> 0)) q [r p])
  (valid! ((r * (p -> q)) -> 0) q [r p])

  undercut rebutter => true
  (valid! (s -> ((r -> (q -> 0)) -> 0)) q [r s])
  ;; this is true due to the non-constructive nature
  ;; s true => (by the undercut)
  ;; - (r -> - q) true => (since r true)
  ;; - q false => (lem)
  ;; q true
  ;; when we dismiss lem, the final derivation does not hold

  support and undercut rebutter => true
  (valid! ((p -> q) * (s -> ((r -> (q -> 0)) -> 0))) q [r s p])

  ;; higher-order support (the fact that p supports q, supports r)
  only p is taken as fact => false
  (valid! ((p -> q) -> r) r [p])
  (p -> q) is taken as fact => true
  (valid! ((p -> q) -> r) r [(p -> q)])

  ;; the fact that p supports both r and s,
  ;; and both r and s supports q,
  ;; therefore q
  (valid! ((p -> (r * s)) * ((r * s) -> q)) q [p])
  ;; equivalently
  (valid! (((p -> r) * (r -> q)) * ((p -> s) * (s -> q))) q [p])
  ;; in fact half of the argumentation suffice
  (valid! ((p -> r) * (r -> q)) q [p])

  (valid! ((p -> (q + r)) * (r -> 0)) q [p])

  ;; the fact that p suggests r or s,
  ;; in either case, q
  (valid! ((p -> (r + s)) * ((r + s) -> q)) q [p])

  ;; higher order claim
  (valid! (q -> p) (p -> q) [q])

  )
