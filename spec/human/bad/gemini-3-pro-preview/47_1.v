Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lra. (* Required for solving real number inequalities *)
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

Example problem_47_example : problem_47_spec [3; 1; 2; 4; 5] 3.
Proof.
  unfold problem_47_spec.
  (* Provide the sorted version of the list *)
  exists [1; 2; 3; 4; 5].
  
  split.
  - (* Prove the list is Sorted *)
    (* repeat constructor handles Sorted_cons, HdRel_cons, etc. *)
    (* try lra handles the Rle inequalities *)
    repeat (constructor; try lra).
  
  - (* Prove the permutation and median properties *)
    (* We use 'x' instead of 'r' to avoid potential naming conflicts if 'r' is reserved or used *)
    intros x.
    split.
    + (* Prove that the elements are the same (In equivalence) *)
      simpl.
      tauto.
      
    + (* Prove the median calculation logic *)
      simpl.
      split.
      * (* Case: Odd length (5 mod 2 = 1) *)
        intro H_odd.
        (* nth 2 [1; 2; 3; 4; 5] 0 is 3 *)
        reflexivity.
        
      * (* Case: Even length (5 mod 2 = 0) *)
        intro H_even.
        (* 1 = 0 is false, so this case is impossible *)
        discriminate.
Qed.