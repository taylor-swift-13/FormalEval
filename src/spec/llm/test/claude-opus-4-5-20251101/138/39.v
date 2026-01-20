Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) (result : bool) : Prop :=
  result = true <-> (n >= 8 /\ Z.even n = true /\ 
    exists a b c d : Z, a > 0 /\ b > 0 /\ c > 0 /\ d > 0 /\
                        Z.even a = true /\ Z.even b = true /\ 
                        Z.even c = true /\ Z.even d = true /\
                        n = a + b + c + d).

Example test_is_equal_to_sum_even_2 : is_equal_to_sum_even_spec 2 false.
Proof.
  unfold is_equal_to_sum_even_spec.
  split.
  - intros H. discriminate H.
  - intros [Hge8 [Heven [a [b [c [d [Ha [Hb [Hc [Hd [Hea [Heb [Hec [Hed Hsum]]]]]]]]]]]]]].
    lia.
Qed.