Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Fourier.
Import ListNotations.
Open Scope R_scope.

Definition is_pos (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter is_pos l.

Example test_get_positive : 
  get_positive_spec 
    [0%Z; -1.25%R; -1.6712853697787629%R; -0.75%R; -2.25%R; -1%Z; -2%Z; -4%Z; -9%Z; -5%Z; -3%Z; -2.25%R; 0%Z] 
    [].
Proof.
  unfold get_positive_spec, filter, is_pos.
  repeat match goal with
  | [ |- context [Rgt_dec ?x 0] ] =>
      destruct (Rgt_dec x 0) as [Hgt | Hle];
      [ exfalso;
        simpl in Hgt;
        try (apply Rgt_irrefl in Hgt; assumption);
        fourier
      | ]
  end.
  reflexivity.
Qed.