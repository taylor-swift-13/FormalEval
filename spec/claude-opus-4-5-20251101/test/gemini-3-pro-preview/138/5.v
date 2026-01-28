Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) (result : bool) : Prop :=
  result = true <-> (n >= 8 /\ Z.even n = true /\ 
    exists a b c d : Z, a > 0 /\ b > 0 /\ c > 0 /\ d > 0 /\
                        Z.even a = true /\ Z.even b = true /\ 
                        Z.even c = true /\ Z.even d = true /\
                        n = a + b + c + d).

Example test_case_1 : is_equal_to_sum_even_spec 11 false.
Proof.
  unfold is_equal_to_sum_even_spec.
  split.
  - intros H.
    discriminate H.
  - intros [_ [H_even _]].
    simpl in H_even.
    discriminate H_even.
Qed.