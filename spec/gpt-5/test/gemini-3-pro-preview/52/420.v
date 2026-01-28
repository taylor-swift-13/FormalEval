Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Rlt x t) l) /\
  (res = false <-> exists x, In x l /\ Rle t x).

Example test_below_threshold : below_threshold_spec [0.2; 62.5; -63.579573934400166; 0.5; 98.82739614126038; -0.28791951724548404; -50.78504214587984; 58.062454697705476; 55.110190228263775; 10.520189946545017] 0 false.
Proof.
  set (l := [0.2; 62.5; -63.579573934400166; 0.5; 98.82739614126038; -0.28791951724548404; -50.78504214587984; 58.062454697705476; 55.110190228263775; 10.520189946545017]).
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H. discriminate H.
    + intros H.
      rewrite Forall_forall in H.
      assert (In 0.2 l).
      { subst l. simpl. left. reflexivity. }
      specialize (H _ H0).
      lra.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      exists 0.2.
      split.
      * subst l. simpl. left. reflexivity.
      * lra.
    + intros _. reflexivity.
Qed.