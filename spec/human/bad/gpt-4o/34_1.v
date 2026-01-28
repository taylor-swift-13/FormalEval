Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Mergesort.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no additional constraints for `unique` by default *)
Definition problem_34_pre (input : list Z) : Prop := True.

(* Specification for problem_34 (returning sorted unique elements) *)
Definition problem_34_spec (input output : list Z) : Prop :=
  Sorted Z.le output /\
  NoDup output /\
  (forall z, In z input <-> In z output).

(* The specified function that should return a sorted and unique list *)
Definition unique (l : list Z) : list Z :=
  sort Z.le (nodup Z.eq_dec l).

(* Example proof for the test case *)
Example problem_34_test_case :
  let input := [5%Z; 3%Z; 5%Z; 2%Z; 3%Z; 3%Z; 9%Z; 0%Z; 123%Z] in
  let output := [0%Z; 2%Z; 3%Z; 5%Z; 9%Z; 123%Z] in
  problem_34_spec input output.
Proof.
  unfold problem_34_spec.
  split.
  - (* Show that the output is sorted *)
    apply Sorted_cons; [lia | ].
    apply Sorted_cons; [lia | ].
    apply Sorted_cons; [lia | ].
    apply Sorted_cons; [lia | ].
    apply Sorted_cons; [lia | ].
    apply Sorted_nil.
  - split.
    + (* Show that the output has unique elements *)
      repeat constructor; intros contra; inversion contra; subst; contradiction.
    + (* Show that input and output have same elements *)
      intros z; split; intros H.
      * (* Forward direction: from input to output *)
        simpl in H.
        repeat (destruct H as [H | H]; subst; simpl; try (left; reflexivity); try right).
        -- now right.
        -- contradiction.
        -- contradiction.
        -- contradiction.
        -- contradiction.
      * (* Backward direction: from output to input *)
        simpl.
        repeat (destruct H as [H | H]; [subst; repeat (try solve [left; reflexivity]); right | ]); try (right; subst).
        contradiction.
Qed.