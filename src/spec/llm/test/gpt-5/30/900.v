Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition Rgtb (x y : R) : bool :=
  if Rlt_dec y x then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgtb x 0) l.

Example get_positive_spec_test :
  get_positive_spec
    [5.803598881698951%R; 25.221353337136023%R; 33.195768044846155%R; -2.25%R; -2.25%R]
    [5.803598881698951%R; 25.221353337136023%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  unfold Rgtb.
  assert (H1 : 0%R < 5.803598881698951%R) by lra.
  destruct (Rlt_dec 0%R 5.803598881698951%R) as [Hpos1|Hnpos1].
  - simpl.
    assert (H2 : 0%R < 25.221353337136023%R) by lra.
    destruct (Rlt_dec 0%R 25.221353337136023%R) as [Hpos2|Hnpos2].
    + simpl.
      assert (H3 : 0%R < 33.195768044846155%R) by lra.
      destruct (Rlt_dec 0%R 33.195768044846155%R) as [Hpos3|Hnpos3].
      * simpl.
        destruct (Rlt_dec 0%R (-2.25%R)) as [Hpos4|Hnpos4].
        { exfalso; lra. }
        simpl.
        destruct (Rlt_dec 0%R (-2.25%R)) as [Hpos5|Hnpos5].
        { exfalso; lra. }
        simpl. reflexivity.
      * exfalso; lra.
    + exfalso; lra.
  - exfalso; lra.
Qed.