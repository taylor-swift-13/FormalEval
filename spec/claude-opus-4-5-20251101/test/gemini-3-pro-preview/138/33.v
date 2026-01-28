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

Example test_case_1 : is_equal_to_sum_even_spec 29 false.
Proof.
  unfold is_equal_to_sum_even_spec.
  split.
  - (* Direction: false = true -> ... *)
    intros H.
    discriminate H.
  - (* Direction: (29 >= 8 /\ Z.even 29 = true /\ ...) -> false = true *)
    intros [_ [Heven _]].
    (* Heven is Z.even 29 = true, but Z.even 29 is false *)
    simpl in Heven.
    discriminate Heven.
Qed.