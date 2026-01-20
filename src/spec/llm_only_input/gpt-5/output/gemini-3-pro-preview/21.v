Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition model (inp : list (list R)) : list R :=
  match inp with
  | ((x :: y :: nil) :: nil) =>
      if Rlt_dec x y then [0.0%R; 1.0%R] else [1.0%R; 0.0%R]
  | _ => []
  end.

Example test_case_model :
  model [[2.0%R; 49.9%R]] = [0.0%R; 1.0%R].
Proof.
  unfold model; simpl.
  destruct (Rlt_dec 2.0%R 49.9%R) as [Hlt | Hnlt].
  - reflexivity.
  - exfalso. apply Hnlt. lra.
Qed.