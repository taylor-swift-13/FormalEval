Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope R_scope.

(* Pre: input must be non-empty to define median *)
Definition problem_47_pre (input : list R) : Prop := input <> [].

Definition problem_47_spec(input : list R) (output : R) : Prop :=
  exists Sorted_input,
    Sorted Rle Sorted_input /\
    (forall r : R, In r input <-> In r Sorted_input) /\
    let len := length input in
    let halflen := ((length input) / 2)%nat in
    ((len mod 2 = 1)%nat -> output = nth halflen Sorted_input 0) /\
    ((len mod 2 = 0)%nat -> output = ((nth halflen Sorted_input 0) + (nth (halflen-1) Sorted_input 0)) / 2).

(* Helper lemma for Rle *)
Lemma IZR_Rle : forall n m : Z, (n <= m)%Z -> IZR n <= IZR m.
Proof.
  intros n m H.
  apply IZR_le. exact H.
Qed.

Example test_median_1 :
  problem_47_spec [IZR 3; IZR 1; IZR 2; IZR 4; IZR 5] (IZR 3).
Proof.
  unfold problem_47_spec.
  exists [IZR 1; IZR 2; IZR 3; IZR 4; IZR 5].
  split.
  - (* Sorted Rle [1; 2; 3; 4; 5] *)
    repeat constructor; apply IZR_Rle; lia.
  - split.
    + (* forall r, In r input <-> In r Sorted_input *)
      intro r.
      simpl.
      tauto.
    + simpl.
      split.
      * intro H. reflexivity.
      * intro H. discriminate H.
Qed.