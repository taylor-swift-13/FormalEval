Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope Z_scope.
Open Scope R_scope.

Inductive num : Type :=
| NInt : Z -> num
| NReal : R -> num.

Definition pos_num (n : num) : bool :=
  match n with
  | NInt z => Z.gtb z 0
  | NReal r => if Rlt_dec 0 r then true else false
  end.

Definition get_positive_spec (l : list num) (res : list num) : Prop :=
  res = filter pos_num l.

Example get_positive_spec_test :
  get_positive_spec
    [NInt (-3%Z); NReal (1%R / 2%R); NInt (-4%Z); NReal (5%R / 2%R); NInt (5%Z);
     NReal ((-11)%R / 5%R); NInt (-8%Z); NInt (-4%Z); NInt (-7%Z);
     NReal ((-21)%R / 2%R); NReal (99%R / 10%R); NReal ((-21)%R / 2%R)]
    [NReal (1%R / 2%R); NReal (5%R / 2%R); NInt (5%Z); NReal (99%R / 10%R)].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0 (1%R / 2%R)) as [H1|H1]; [| exfalso; lra].
  simpl.
  destruct (Rlt_dec 0 (5%R / 2%R)) as [H2|H2]; [| exfalso; lra].
  simpl.
  destruct (Rlt_dec 0 ((-11)%R / 5%R)) as [H3|H3]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 ((-21)%R / 2%R)) as [H4|H4]; [exfalso; lra|].
  simpl.
  destruct (Rlt_dec 0 (99%R / 10%R)) as [H5|H5]; [| exfalso; lra].
  simpl.
  destruct (Rlt_dec 0 ((-21)%R / 2%R)) as [H6|H6]; [exfalso; lra|].
  simpl.
  reflexivity.
Qed.