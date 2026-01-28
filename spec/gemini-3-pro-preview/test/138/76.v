Require Import Coq.ZArith.ZArith.
Require Import Psatz.
Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) (res : bool) : Prop :=
  res = true <-> (n >= 8 /\ n mod 2 = 0).

Example test_case_1 : is_equal_to_sum_even_spec 103 false.
Proof.
  unfold is_equal_to_sum_even_spec.
  split.
  - intros H.
    discriminate H.
  - intros [Hge Hmod].
    (* Simplify the modulo expression for the concrete value 103 *)
    compute in Hmod.
    (* Hmod becomes 1 = 0, which is a contradiction *)
    discriminate Hmod.
Qed.