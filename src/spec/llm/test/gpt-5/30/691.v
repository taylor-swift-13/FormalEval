Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [9.9%R; 25.12472520208241%R; 33.195768044846155%R; -2.25%R; 9.9%R]
                    [9.9%R; 25.12472520208241%R; 33.195768044846155%R; 9.9%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0 9.9%R) as [_|H]; [|exfalso; lra].
  simpl.
  destruct (Rlt_dec 0 25.12472520208241%R) as [_|H]; [|exfalso; lra].
  simpl.
  destruct (Rlt_dec 0 33.195768044846155%R) as [_|H]; [|exfalso; lra].
  simpl.
  destruct (Rlt_dec 0 (-2.25%R)) as [H|_]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 9.9%R) as [_|H]; [|exfalso; lra].
  simpl.
  reflexivity.
Qed.