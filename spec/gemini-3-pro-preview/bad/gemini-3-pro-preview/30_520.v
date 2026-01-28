Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Classes.RelationClasses.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example test_get_positive : get_positive_spec [0.5%R; -4%Z; 2.5%R; 5%Z; -2.2%R; -8%Z; -7%Z; 9.9%R; -11.18889279027017%R; -10.5%R] [0.5%R; 2.5%R; 5%Z; 9.9%R].
Proof.
  unfold get_positive_spec.
  repeat match goal with
  | [ |- context[Rlt_dec 0 ?x] ] => destruct (Rlt_dec 0 x); try lra
  end.
  simpl.
  reflexivity.
Qed.