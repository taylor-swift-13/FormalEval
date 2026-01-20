Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [33.195768044846155%R; -2.25%R] [33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0 33.195768044846155%R) as [Hpos | Hnpos].
  - simpl.
    destruct (Rlt_dec 0 (-2.25%R)) as [Hpos2 | Hnpos2].
    + exfalso. lra.
    + simpl. reflexivity.
  - exfalso. apply Hnpos. lra.
Qed.