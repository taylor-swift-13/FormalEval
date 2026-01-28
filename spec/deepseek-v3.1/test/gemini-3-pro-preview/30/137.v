Require Import List.
Require Import ZArith.
Require Import Reals.
Require Import Lra.
Import ListNotations.

(* Opening R_scope is necessary to interpret real literals like 0.5 *)
Open Scope R_scope.

Definition get_positive_spec (l : list R) (result : list R) : Prop :=
  result = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive:
  get_positive_spec [0.5; -4; 2.5; 5; -2.2; -8; -4; -7; -10.5; 9.9; -10.5] [0.5; 2.5; 5; 9.9].
Proof.
  (* Unfold the specification definition *)
  unfold get_positive_spec.
  
  (* Simplify the filter operations *)
  simpl.
  
  (* Solve the real inequalities to reduce the terms *)
  repeat (match goal with
          | |- context [Rgt_dec ?x ?y] => destruct (Rgt_dec x y); try lra
          end).
  
  (* Prove equality *)
  reflexivity.
Qed.