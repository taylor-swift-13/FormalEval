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

Example test_case : generate_integers_spec 1 99997 [2; 4; 6; 8].
Proof.
  unfold generate_integers_spec.
  simpl Z.min. simpl Z.max.
  split.
  - (* Prove Sorted Z.lt [2; 4; 6; 8] *)
    repeat constructor; try lia.
  - (* Prove the logical equivalence *)
    intros x. split.
    + (* Forward direction: In list -> satisfies conditions *)
      intros H_in.
      simpl in H_in.
      destruct H_in as [H | [H | [H | [H | H]]]].
      * (* x = 2 *)
        rewrite <- H. split; [lia | split; [lia | reflexivity]].
      * (* x = 4 *)
        rewrite <- H. split; [lia | split; [lia | reflexivity]].
      * (* x = 6 *)
        rewrite <- H. split; [lia | split; [lia | reflexivity]].
      * (* x = 8 *)
        rewrite <- H. split; [lia | split; [lia | reflexivity]].
      * (* False case *)
        contradiction.
    + (* Backward direction: satisfies conditions -> In list *)
      intros [H_range [H_bound H_even]].
      (* H_range: 1 <= x <= 99997, H_bound: x < 10 *)
      (* Enumerate possible integer values for x in the range [1, 9] *)
      assert (H_enum: x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9) by lia.
      
      destruct H_enum as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]].
      * (* x = 1 *)
        simpl in H_even; discriminate.
      * (* x = 2 *)
        simpl; left; reflexivity.
      * (* x = 3 *)
        simpl in H_even; discriminate.
      * (* x = 4 *)
        simpl; right; left; reflexivity.
      * (* x = 5 *)
        simpl in H_even; discriminate.
      * (* x = 6 *)
        simpl; right; right; left; reflexivity.
      * (* x = 7 *)
        simpl in H_even; discriminate.
      * (* x = 8 *)
        simpl; right; right; right; left; reflexivity.
      * (* x = 9 *)
        simpl in H_even; discriminate.
Qed.