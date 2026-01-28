Require Import ZArith.
Require Import Psatz.
Open Scope Z_scope.

Definition choose_num_spec (x y result : Z) : Prop :=
  (x > y -> result = -1) /\
  (x <= y ->
    ((exists k, x <= k <= y /\ k mod 2 = 0) ->
      result mod 2 = 0 /\
      x <= result <= y /\
      (forall k, x <= k <= y -> k mod 2 = 0 -> k <= result)) /\
    ((~exists k, x <= k <= y /\ k mod 2 = 0) -> result = -1)).

Example test_case : choose_num_spec 31 31 (-1).
Proof.
  unfold choose_num_spec.
  split.
  - intros H.
    lia.
  - intros Hle.
    split.
    + intros [k [Hrange Heven]].
      assert (k = 31) by lia.
      subst k.
      vm_compute in Heven.
      discriminate.
    + intros Hnot_ex.
      reflexivity.
Qed.