Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope R_scope.

(* Pre: no special constraints for `incr_list` *)
Definition problem_42_pre (input : list R) : Prop := True.

(* Note: explicitly use %nat for the length comparison to avoid conflict with R_scope *)
Definition problem_42_spec(input output : list R) : Prop :=
  length input = length output /\
  forall i : nat, (i < length output)%nat -> nth i output 0 = (nth i input 0 + 1).

(* Test case *)
Example problem_42_example : problem_42_spec 
  [2.443642398169077; 5.870022616692514; -40; 0.5090263789060623; 0; 5.9; 8.6; 3.8] 
  [3.443642398169077; 6.870022616692514; -39; 1.5090263789060623; 1; 6.9; 9.6; 4.8].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    repeat (destruct i; [ simpl; lra | ]).
    simpl in H.
    lia.
Qed.