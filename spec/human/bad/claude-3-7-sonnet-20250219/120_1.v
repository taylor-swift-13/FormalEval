Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Definition problem_120_pre (arr : list Z) (k : nat) : Prop :=
       (length arr >= 1)%nat /\ (length arr <= 1000)%nat /\
       Forall (fun z => (-1000 <= z /\ z <= 1000)) arr /\
       (k <= length arr)%nat.

Definition problem_120_spec (arr : list Z) (k : nat) (res : list Z) : Prop :=
  length res = k /\
  Sorted Z.le res /\
  (exists rest_of_arr,
    Permutation (res ++ rest_of_arr) arr /\
    (forall x y, In x res -> In y rest_of_arr -> y <= x)).

Example problem_120_example1 :
  problem_120_spec [-3; -4; 5] 3 [-4; -3; 5].
Proof.
  unfold problem_120_spec.
  split.
  - reflexivity.
  split.
  - repeat constructor; lia.
  - exists [].
    split.
    + simpl.
      apply (Permutation_trans _ ( -3 :: -4 :: 5 :: []) );
      [ apply Permutation_swap | apply Permutation_refl].
    + intros x y Hx Hy. simpl in Hy. contradiction.
Qed.