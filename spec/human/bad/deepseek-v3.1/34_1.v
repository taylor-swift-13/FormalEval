Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Definition problem_34_spec (input : list Z) (output : list Z) : Prop :=
  Sorted Z.le output /\
  NoDup output /\
  (forall z, In z input <-> In z output).

Lemma output_sorted : Sorted Z.le [0%Z; 2%Z; 3%Z; 5%Z; 9%Z; 123%Z].
Proof.
  repeat constructor; lia.
Qed.

Lemma output_nodup : NoDup [0%Z; 2%Z; 3%Z; 5%Z; 9%Z; 123%Z].
Proof.
  repeat constructor; simpl; intuition lia.
Qed.

Lemma same_elements : forall z : Z, 
  In z [5%Z; 3%Z; 5%Z; 2%Z; 3%Z; 3%Z; 9%Z; 0%Z; 123%Z] <-> In z [0%Z; 2%Z; 3%Z; 5%Z; 9%Z; 123%Z].
Proof.
  intro z; split; intro H.
  - simpl in H; repeat (destruct H as [H|H]; try (subst z; simpl; auto)).
    contradiction.
  - simpl in H; repeat (destruct H as [H|H]; try (subst z; simpl; auto)).
    contradiction.
Qed.

Example unique_example : 
  problem_34_spec [5%Z; 3%Z; 5%Z; 2%Z; 3%Z; 3%Z; 9%Z; 0%Z; 123%Z] [0%Z; 2%Z; 3%Z; 5%Z; 9%Z; 123%Z].
Proof.
  unfold problem_34_spec.
  split. 
  - apply output_sorted.
  - split.
    + apply output_nodup.
    + apply same_elements.
Qed.