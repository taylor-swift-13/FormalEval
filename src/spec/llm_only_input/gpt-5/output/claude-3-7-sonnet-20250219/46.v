Require Import ZArith Lia.
Open Scope Z_scope.

Definition fib4_spec (n : Z) (result : Z) : Prop :=
  (n = 0 /\ result = 0) \/
  (n = 1 /\ result = 0) \/
  (n = 2 /\ result = 2) \/
  (n = 3 /\ result = 0) \/
  (n >= 4 /\
   exists a b c d i,
     a = 0 /\ b = 0 /\ c = 2 /\ d = 0 /\
     i = 4 /\
     (forall k, 4 <= k <= n ->
       exists a' b' c' d',
         a' = b /\
         b' = c /\
         c' = d /\
         d' = a + b + c + d /\
         (a, b, c, d) = (a', b', c', d')) /\
     d = result).

Example fib4_spec_test : ~ fib4_spec 5%Z 4%Z.
Proof.
  intros H.
  unfold fib4_spec in H.
  destruct H as
    [ [Hn0 Hr0]
    | [ [Hn1 Hr1]
      | [ [Hn2 Hr2]
        | [ [Hn3 Hr3]
          | [Hge4 Hex]
          ]
        ]
      ]
    ].
  - lia.
  - lia.
  - lia.
  - lia.
  - destruct Hex as (a & b & c & d & i & Ha & Hb & Hc & Hd & Hi & Hforall & Hres).
    subst.
    lia.
Qed.