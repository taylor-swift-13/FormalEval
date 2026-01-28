Require Import Coq.ZArith.ZArith.
Require Import Psatz.
Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) (res : bool) : Prop :=
  res = true <-> (n >= 8 /\ n mod 2 = 0).

Example test_case_1 : is_equal_to_sum_even_spec 9 false.
Proof.
  unfold is_equal_to_sum_even_spec.
  split.
  - intros H.
    discriminate H.
  - intros [Hge Hmod].
    (* The hypothesis Hmod asserts 9 mod 2 = 0. *)
    (* Computing 9 mod 2 evaluates to 1, resulting in 1 = 0. *)
    compute in Hmod.
    discriminate Hmod.
Qed.