Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition is_positive (x : R) : bool :=
  if Rlt_dec 0 x then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter is_positive l.

Example test_get_positive : get_positive_spec [0.5; -1.6451572106484336; -4; 2.5; -8; 7.7; 9.9; -10.5; 9.9; -13.662203687087855] [0.5; 2.5; 7.7; 9.9; 9.9].
Proof.
  unfold get_positive_spec, is_positive.
  simpl.
  repeat match goal with
  | |- context [Rlt_dec 0 ?x] => destruct (Rlt_dec 0 x); [ try lra | try lra ]
  end.
  reflexivity.
Qed.