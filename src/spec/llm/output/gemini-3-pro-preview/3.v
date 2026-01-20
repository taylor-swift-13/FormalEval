Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_empty : below_zero_spec [] false.
Proof.
  unfold below_zero_spec.
  split.
  - (* Left to right implication: false = true -> ... *)
    intros H.
    inversion H.
  - (* Right to left implication: (exists n, ...) -> false = true *)
    intros [n [Hbounds _]].
    (* Simplify the length of the empty list to 0 *)
    simpl in Hbounds.
    (* The bounds (0 < n <= 0)%nat are impossible *)
    lia.
Qed.