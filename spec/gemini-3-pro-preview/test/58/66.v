Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Definition bool_le (b1 b2 : bool) : Prop :=
  match b1, b2 with
  | false, _ => True
  | true, true => True
  | true, false => False
  end.

Definition common_spec (l1 l2 res : list bool) : Prop :=
  Sorted bool_le res /\
  NoDup res /\
  (forall x : bool, In x res <-> (In x l1 /\ In x l2)).

Example test_common_spec :
  common_spec 
    [false; true] 
    [false; true] 
    [false; true].
Proof.
  unfold common_spec.
  split.
  - (* Sorted *)
    repeat constructor.
  - split.
    + (* NoDup *)
      repeat constructor; simpl; intro H; 
      repeat (destruct H as [H|H]; [try discriminate | ]); contradiction.
    + (* Equivalence *)
      intros x. split.
      * (* -> *)
        intro H. simpl in H.
        repeat (destruct H as [H|H]; [subst; simpl; tauto | ]); contradiction.
      * (* <- *)
        intros [H1 H2]. simpl in H1.
        repeat (destruct H1 as [H1|H1]; [
          subst; simpl in H2; simpl; tauto
        | ]); contradiction.
Qed.