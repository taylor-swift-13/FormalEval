Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope R_scope.

(* Pre: no special constraints for `incr_list` *)
Definition problem_42_pre (input : list R) : Prop := True.

(* Note: explicitly use %nat for the length comparison *)
Definition problem_42_spec(input output : list R) : Prop :=
  length input = length output /\
  forall i : nat, (i < length output)%nat -> nth i output 0%R = ((nth i input 0%R) + 1)%R.

(* Test case: input = [0.5; ...], output = [1.5; ...] *)
Example problem_42_example : problem_42_spec 
  [0.5; 88.08080880531568; -21.596861567647125; 0.14907947235135702; -59.15962684129501; -0.6821906440453559; -0.6752788781109065; -4.166307314246723; 0.14907947235135702]
  [1.5; 89.08080880531568; -20.596861567647125; 1.14907947235135702; -58.15962684129501; 0.3178093559546441; 0.3247211218890935; -3.166307314246723; 1.14907947235135702].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 9 (destruct i; [simpl; lra | ]).
    (* Index out of bounds *)
    simpl in H.
    lia.
Qed.