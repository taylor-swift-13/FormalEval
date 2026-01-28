Require Import Coq.Lists.List.
Require Import Coq.Floats.Floats.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope float_scope.

(* Pre: no special constraints for `incr_list` *)
Definition problem_42_pre (input : list float) : Prop := True.

(* Note: explicitly use %nat for the length comparison to avoid conflict with float_scope *)
Definition problem_42_spec(input output : list float) : Prop :=
  length input = length output /\
  forall i : nat, (i < length output)%nat -> nth i output 0%float = (nth i input 0%float + 1%float).

(* Test case: input = [3.5652526206208957; 3.7; 8.9; 0.5; 8.9], output = [4.565252620620896; 4.7; 9.9; 1.5; 9.9] *)
Example problem_42_example : problem_42_spec 
  [3.5652526206208957; 3.7; 8.9; 0.5; 8.9] 
  [4.565252620620896; 4.7; 9.9; 1.5; 9.9].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    simpl in H.
    (* Verify equality for each element using float computation *)
    do 5 (destruct i; [vm_compute; reflexivity | ]).
    (* Handle out of bounds *)
    lia.
Qed.