Require Import Coq.ZArith.ZArith.
Require Import Psatz.
Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) (res : bool) : Prop :=
  res = true <-> (n >= 8 /\ n mod 2 = 0).

Example test_case_1 : is_equal_to_sum_even_spec 105 false.
Proof.
  unfold is_equal_to_sum_even_spec.
  split.
  - (* Case: false = true -> ... *)
    intros H.
    discriminate H.
  - (* Case: ... -> false = true *)
    intros [Hge Hmod].
    (* Hmod is 105 mod 2 = 0. We compute 105 mod 2 to show contradiction. *)
    assert (Hcalc: 105 mod 2 = 1) by reflexivity.
    rewrite Hcalc in Hmod.
    discriminate Hmod.
Qed.