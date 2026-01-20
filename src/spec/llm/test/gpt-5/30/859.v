Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example get_positive_spec_test :
  get_positive_spec
    [-2.651030586877352%R; 9.9%R; 25.221353337136023%R; 24.93175152910768%R;
     -0.42322814636615796%R; 33.195768044846155%R; -2.6307909667819085%R; -2.25%R]
    [9.9%R; 25.221353337136023%R; 24.93175152910768%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  assert (Hn1: ~ (-2.651030586877352%R > 0%R)) by lra.
  destruct (Rgt_dec (-2.651030586877352%R) 0%R) as [H|H]; [exfalso; apply Hn1; exact H|].
  simpl.
  assert (Hp1: 9.9%R > 0%R) by lra.
  destruct (Rgt_dec 9.9%R 0%R) as [H2|H2]; [|exfalso; apply H2; exact Hp1].
  simpl.
  assert (Hp2: 25.221353337136023%R > 0%R) by lra.
  destruct (Rgt_dec 25.221353337136023%R 0%R) as [H3|H3]; [|exfalso; apply H3; exact Hp2].
  simpl.
  assert (Hp3: 24.93175152910768%R > 0%R) by lra.
  destruct (Rgt_dec 24.93175152910768%R 0%R) as [H4|H4]; [|exfalso; apply H4; exact Hp3].
  simpl.
  assert (Hn2: ~ (-0.42322814636615796%R > 0%R)) by lra.
  destruct (Rgt_dec (-0.42322814636615796%R) 0%R) as [H5|H5]; [exfalso; apply Hn2; exact H5|].
  simpl.
  assert (Hp4: 33.195768044846155%R > 0%R) by lra.
  destruct (Rgt_dec 33.195768044846155%R 0%R) as [H6|H6]; [|exfalso; apply H6; exact Hp4].
  simpl.
  assert (Hn3: ~ (-2.6307909667819085%R > 0%R)) by lra.
  destruct (Rgt_dec (-2.6307909667819085%R) 0%R) as [H7|H7]; [exfalso; apply Hn3; exact H7|].
  simpl.
  assert (Hn4: ~ (-2.25%R > 0%R)) by lra.
  destruct (Rgt_dec (-2.25%R) 0%R) as [H8|H8]; [exfalso; apply Hn4; exact H8|].
  simpl.
  reflexivity.
Qed.