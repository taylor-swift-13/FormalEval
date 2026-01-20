Require Import ZArith.
Require Import Bool.
Require Import Psatz. (* Required for lia tactic *)

Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) (result : bool) : Prop :=
  result = true <-> (n >= 8 /\ Z.even n = true /\ 
    exists a b c d : Z, a > 0 /\ b > 0 /\ c > 0 /\ d > 0 /\
                        Z.even a = true /\ Z.even b = true /\ 
                        Z.even c = true /\ Z.even d = true /\
                        n = a + b + c + d).

Example test_case_1 : is_equal_to_sum_even_spec 4 false.
Proof.
  unfold is_equal_to_sum_even_spec.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate H.
  - (* Right to Left: (4 >= 8 /\ ...) -> false = true *)
    intros [H_ge _].
    (* The hypothesis H_ge states 4 >= 8, which is false. *)
    lia.
Qed.