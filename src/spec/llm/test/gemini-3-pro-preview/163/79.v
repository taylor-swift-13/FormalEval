Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition generate_integers_spec (a b : Z) (l : list Z) : Prop :=
  let lower := Z.min a b in
  let upper := Z.max a b in
  Sorted Z.lt l /\
  (forall x : Z, In x l <-> lower <= x <= upper /\ x < 10 /\ Z.even x = true).

Example test_case : generate_integers_spec 6 6 [6].
Proof.
  unfold generate_integers_spec.
  simpl Z.min. simpl Z.max.
  split.
  - (* Prove Sorted Z.lt [6] *)
    repeat constructor; try lia.
  - (* Prove the logical equivalence *)
    intros x. split.
    + (* Forward direction: In list -> satisfies conditions *)
      intros H_in.
      simpl in H_in.
      destruct H_in as [H | H].
      * (* x = 6 *)
        rewrite <- H. split; [lia | split; [lia | reflexivity]].
      * (* False case *)
        contradiction.
    + (* Backward direction: satisfies conditions -> In list *)
      intros [H_range [H_bound H_even]].
      (* H_range: 6 <= x <= 6 implies x = 6 *)
      assert (H_eq: x = 6) by lia.
      rewrite H_eq.
      simpl. left. reflexivity.
Qed.