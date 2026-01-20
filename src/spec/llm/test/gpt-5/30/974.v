Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec
    [0.5%R; -1.6451572106484336%R; -4%R; 2.5%R; -8%R; 7.7%R; 9.9%R; -10.5%R; 9.9%R; -13.662203687087855%R]
    [0.5%R; 2.5%R; 7.7%R; 9.9%R; 9.9%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0 0.5%R) as [H0|H0]; [| exfalso; lra].
  simpl.
  destruct (Rlt_dec 0 (-1.6451572106484336%R)) as [H1|H1]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 (-4%R)) as [H2|H2]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 2.5%R) as [H3|H3]; [| exfalso; lra].
  simpl.
  destruct (Rlt_dec 0 (-8%R)) as [H4|H4]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 7.7%R) as [H5|H5]; [| exfalso; lra].
  simpl.
  destruct (Rlt_dec 0 9.9%R) as [H6|H6]; [| exfalso; lra].
  simpl.
  destruct (Rlt_dec 0 (-10.5%R)) as [H7|H7]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 9.9%R) as [H8|H8]; [| exfalso; lra].
  simpl.
  destruct (Rlt_dec 0 (-13.662203687087855%R)) as [H9|H9]; [exfalso; lra|].
  simpl.
  reflexivity.
Qed.