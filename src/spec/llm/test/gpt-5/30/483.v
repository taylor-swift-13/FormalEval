Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [0%R; -1.25%R; -1.5%R; -2.25%R; -2%R; -3%R; -5%R; -6%R; -3%R] [].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat match goal with
  | |- context [if Rlt_dec 0 ?x then _ else _] =>
      destruct (Rlt_dec 0 x); [exfalso; lra | simpl]
  end.
  reflexivity.
Qed.