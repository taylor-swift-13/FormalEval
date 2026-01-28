Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition is_sorted (l : list Z) : Prop :=
  forall i j, (0 <= i < j)%nat -> (j < length l)%nat ->
    (Z.le (nth i l 0%Z) (nth j l 0%Z)).

Definition no_duplicates {A : Type} (l : list A) : Prop :=
  NoDup l.

Definition is_intersection {A : Type} (l1 l2 result : list A) : Prop :=
  forall x, In x result <-> (In x l1 /\ In x l2).

Definition common_spec (l1 l2 result : list Z) : Prop :=
  is_intersection l1 l2 result /\
  no_duplicates result /\
  is_sorted result.

Example test_common_spec : 
  common_spec 
    [1; 4; 3; 34; 653; 2; 5] 
    [5; 7; 1; 5; 9; 653; 121] 
    [1; 5; 653].
Proof.
  unfold common_spec.
  split.
  - (* Part 1: is_intersection *)
    unfold is_intersection.
    intros x.
    split.
    + (* In result -> In l1 /\ In l2 *)
      intro H.
      simpl in H.
      (* Decompose H: x=1 \/ x=5 \/ x=653 *)
      destruct H as [-> | [-> | [-> | []]]]; simpl; split;
      (* Prove In x l1 and In x l2 by search *)
      repeat (try (left; reflexivity); right).
    + (* In l1 /\ In l2 -> In result *)
      intros [H1 H2].
      simpl in H1.
      (* Decompose H1 to check each element of l1 *)
      destruct H1 as [-> | H1]. { simpl. left. reflexivity. } (* x = 1 *)
      destruct H1 as [-> | H1]. { simpl in H2. lia. } (* x = 4, not in l2 *)
      destruct H1 as [-> | H1]. { simpl in H2. lia. } (* x = 3, not in l2 *)
      destruct H1 as [-> | H1]. { simpl in H2. lia. } (* x = 34, not in l2 *)
      destruct H1 as [-> | H1]. { simpl. right; right; left. reflexivity. } (* x = 653 *)
      destruct H1 as [-> | H1]. { simpl in H2. lia. } (* x = 2, not in l2 *)
      destruct H1 as [-> | H1]. { simpl. right; left. reflexivity. } (* x = 5 *)
      contradiction. (* End of l1 *)
  - split.
    + (* Part 2: no_duplicates *)
      unfold no_duplicates.
      repeat constructor; simpl; intro H; lia.
    + (* Part 3: is_sorted *)
      unfold is_sorted.
      intros i j Hlt Hlen.
      simpl in Hlen.
      (* Enumerate valid indices i and j given the length is 3 *)
      assert (Hj: j = 1%nat \/ j = 2%nat) by lia.
      destruct Hj as [-> | ->].
      * (* Case j = 1, implies i = 0 *)
        assert (Hi: i = 0%nat) by lia.
        subst i. simpl. lia.
      * (* Case j = 2, implies i = 0 or i = 1 *)
        assert (Hi: i = 0%nat \/ i = 1%nat) by lia.
        destruct Hi as [-> | ->]; simpl; lia.
Qed.