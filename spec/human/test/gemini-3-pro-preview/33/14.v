Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition problem_33_pre (input : list Z) : Prop := True.

Definition problem_33_spec (input output : list Z) : Prop :=
  Permutation input output /\
  (forall (i : nat), (i < length input)%nat -> (i mod 3 <> 0) ->
    nth i output 0%Z = nth i input 0%Z) /\
  (forall (i j : nat), i < length output /\ j < length output /\
    i mod 3 = 0 /\ j mod 3 = 0 /\ i < j ->
    (nth i output 0 <= nth j output 0)%Z).

Example test_case_problem_33 : problem_33_spec 
  [3%Z; 6%Z; 9%Z; 12%Z; 15%Z; 18%Z; 21%Z; 24%Z; 27%Z; 30%Z; 33%Z; 36%Z] 
  [3%Z; 6%Z; 9%Z; 12%Z; 15%Z; 18%Z; 21%Z; 24%Z; 27%Z; 30%Z; 33%Z; 36%Z].
Proof.
  unfold problem_33_spec.
  split.
  - apply Permutation_refl.
  - split.
    + intros. reflexivity.
    + intros i j (Hi & Hj & Hmodi & Hmodj & Hlt).
      destruct i as [| [| [| [| [| [| [| [| [| [| [| [| i ]]]]]]]]]]]];
      try (simpl in Hmodi; discriminate);
      try (simpl in Hi; lia);
      destruct j as [| [| [| [| [| [| [| [| [| [| [| [| j ]]]]]]]]]]]];
      try (simpl in Hmodj; discriminate);
      try (simpl in Hj; lia);
      try (simpl in Hlt; lia);
      try (simpl; lia).
Qed.