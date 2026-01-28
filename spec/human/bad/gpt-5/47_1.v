Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope R_scope.

(* Pre: input must be non-empty to define median *)
Definition problem_47_pre (input : list R) : Prop := input <> [].

Definition problem_47_spec(input : list R) (output : R) : Prop :=
  exists Sorted_input,
    Sorted Rle Sorted_input /\
    forall r : R, In r input <-> In r Sorted_input /\
    let len := length input in
    let halflen := ((length input) / 2)%nat in
    ((len mod 2 = 1)%nat -> output = nth halflen Sorted_input 0) /\
    ((len mod 2 = 0)%nat -> output = ((nth halflen Sorted_input 0) + (nth (halflen-1) Sorted_input 0)) / 2).

Example problem_47_test1 :
  problem_47_pre [IZR 3%Z; IZR 1%Z; IZR 2%Z; IZR 4%Z; IZR 5%Z] /\
  problem_47_spec [IZR 3%Z; IZR 1%Z; IZR 2%Z; IZR 4%Z; IZR 5%Z] (IZR 3%Z).
Proof.
  split.
  - unfold problem_47_pre. discriminate.
  - unfold problem_47_spec.
    exists [IZR 1%Z; IZR 2%Z; IZR 3%Z; IZR 4%Z; IZR 5%Z].
    split.
    + (* Prove Sorted Rle for the sorted list *)
      constructor.
      * (* HdRel for head 1 on [2;3;4;5] *)
        constructor; [simpl; lra|].
        constructor; [simpl; lra|].
        constructor; [simpl; lra|].
        constructor; [simpl; lra|].
        constructor.
      * (* Sorted for [2;3;4;5] *)
        constructor.
        -- (* HdRel for head 2 on [3;4;5] *)
           constructor; [simpl; lra|].
           constructor; [simpl; lra|].
           constructor; [simpl; lra|].
           constructor.
        -- (* Sorted for [3;4;5] *)
           constructor.
           ++ (* HdRel for head 3 on [4;5] *)
              constructor; [simpl; lra|].
              constructor; [simpl; lra|].
              constructor.
           ++ (* Sorted for [4;5] *)
              constructor.
              ** (* HdRel for head 4 on [5] *)
                 constructor; [simpl; lra|].
                 constructor.
              ** (* Sorted for [5] *)
                 constructor.
                 --- constructor.
                 --- constructor.
    + (* Membership equivalence bundled with the median property, as per the spec's structure *)
      intros r.
      assert (Hperm: Permutation
                       [IZR 3%Z; IZR 1%Z; IZR 2%Z; IZR 4%Z; IZR 5%Z]
                       [IZR 1%Z; IZR 2%Z; IZR 3%Z; IZR 4%Z; IZR 5%Z]).
      {
        eapply Permutation_trans.
        - apply perm_swap.
        - apply perm_skip. apply perm_swap.
      }
      split.
      * (* -> direction: from membership in input, give membership in sorted list and median conditions *)
        intro Hin.
        split.
        -- eapply Permutation_in; [exact Hperm| exact Hin].
        -- simpl.
           split.
           ++ intros _. reflexivity.
           ++ intros Heven. simpl in Heven. lia.
      * (* <- direction: from membership in sorted list (and median conditions), give membership in input *)
        intros [HinSorted _].
        eapply Permutation_in; [apply Permutation_sym; exact Hperm| exact HinSorted].
Qed.