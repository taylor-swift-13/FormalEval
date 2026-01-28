Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition common_spec (l1 : list Z) (l2 : list Z) (result : list Z) : Prop :=
  exists common_set : list Z,
    NoDup common_set /\
    (forall x : Z, In x common_set <-> (In x l1 /\ In x l2)) /\
    StronglySorted Z.lt common_set /\
    result = common_set.

Example test_common_spec :
  common_spec 
    [1; 4; 3; 34; 653; 2; 5] 
    [5; 7; 1; 5; 9; 653; 121] 
    [1; 5; 653].
Proof.
  unfold common_spec.
  exists [1; 5; 653].
  repeat split.

  (* Goal 1: NoDup *)
  - repeat constructor; simpl; try (intro H; repeat match goal with
      | [ H : _ \/ _ |- _ ] => destruct H
    end; try lia).

  (* Goal 2: Equivalence *)
  - intros x; split.
    + (* Forward: In result -> In l1 /\ In l2 *)
      intro H; simpl in H.
      destruct H as [H | [H | [H | H]]]; subst; split; simpl; auto 20; try contradiction.
    + (* Backward: In l1 /\ In l2 -> In result *)
      intros [H1 H2].
      simpl in H1; simpl in H2.
      repeat match goal with
      | [ H : _ \/ _ |- _ ] => destruct H
      end; subst; simpl; auto; try lia.

  (* Goal 3: StronglySorted *)
  - repeat (constructor; simpl; try lia).

  (* Goal 4: Result equality *)
  - reflexivity.
Qed.