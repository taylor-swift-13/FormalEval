Require Import Coq.ZArith.ZArith.
Require Import Psatz.
Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) (res : bool) : Prop :=
  res = true <-> (n >= 8 /\ n mod 2 = 0).

Example test_case_1 : is_equal_to_sum_even_spec 53 false.
Proof.
  unfold is_equal_to_sum_even_spec.
  split.
  - (* Case: false = true -> ... *)
    intros H.
    discriminate H.
  - (* Case: ... -> false = true *)
    intros H.
    destruct H as [Hge Hmod].
    (* We have 53 mod 2 = 0 in the hypothesis Hmod, which is false *)
    (* Compute reduces 53 mod 2 to 1, turning Hmod into 1 = 0 *)
    compute in Hmod.
    discriminate Hmod.
Qed.