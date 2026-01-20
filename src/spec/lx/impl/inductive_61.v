(* HumanEval 61 - Inductive Spec *)
Require Import Coq.Lists.List Coq.Strings.Ascii.
Import ListNotations.

Inductive check_depth_rel : list ascii -> nat -> nat -> Prop :=
| cdr_empty : forall d, check_depth_rel [] d d
| cdr_open : forall l d d_final, check_depth_rel l (S d) d_final -> check_depth_rel ("("%char :: l) d d_final
| cdr_close : forall l d d_final, d > 0 -> check_depth_rel l d d_final -> check_depth_rel (")"%char :: l) (S d) d_final.

Definition correct_bracketing_spec (brackets : list ascii) (output : bool) : Prop :=
  (output = true <-> exists d, check_depth_rel brackets 0%nat d /\ d = 0%nat).



