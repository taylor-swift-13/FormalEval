Require Import Arith.Arith.

Definition fibfib_spec (n : nat) (res : nat) : Prop :=
  (n = 0 /\ res = 0) \/
  (n = 1 /\ res = 0) \/
  (n = 2 /\ res = 1) \/
  (n >= 3 /\ exists a b c i,
      a = 0 /\ b = 0 /\ c = 1 /\
      i = 3 /\
      (forall k x y z, (3 <= k < n) -> 
        let x' := y in
        let y' := z in
        let z' := x + y + z in
        True) /\
      res = c).

Example fibfib_test_case : fibfib_spec 3 1.
Proof.
  unfold fibfib_spec.
  right. right. right.
  split.
  - apply le_n.
  - exists 0, 0, 1, 3.
    split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|].
    split.
    + intros. trivial.
    + reflexivity.
Qed.