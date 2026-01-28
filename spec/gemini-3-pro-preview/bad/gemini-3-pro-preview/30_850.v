Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition is_pos (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter is_pos l.

Lemma is_pos_true : forall x, x > 0 -> is_pos x = true.
Proof.
  intros. unfold is_pos. destruct (Rgt_dec x 0); auto.
  lra.
Qed.

Lemma is_pos_false : forall x, ~ x > 0 -> is_pos x = false.
Proof.
  intros. unfold is_pos. destruct (Rgt_dec x 0); auto.
  lra.
Qed.

Example test_get_positive : get_positive_spec [9.9; 25.221353337136023; 24.93175152910768; 33.195768044846155; -2.25; -10.338878645170468; 33.195768044846155] [9.9; 25.221353337136023; 24.93175152910768; 33.195768044846155; 33.195768044846155].
Proof.
  unfold get_positive_spec.
  unfold filter.
  replace (is_pos 9.9) with true by (apply is_pos_true; lra).
  replace (is_pos 25.221353337136023) with true by (apply is_pos_true; lra).
  replace (is_pos 24.93175152910768) with true by (apply is_pos_true; lra).
  replace (is_pos 33.195768044846155) with true by (apply is_pos_true; lra).
  replace (is_pos (-2.25)) with false by (apply is_pos_false; lra).
  replace (is_pos (-10.338878645170468)) with false by (apply is_pos_false; lra).
  reflexivity.
Qed.