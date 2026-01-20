Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope Z_scope.
Open Scope R_scope.

Inductive Num : Type :=
| Int : Z -> Num
| Real : R -> Num.

Definition is_pos (n : Num) : bool :=
  match n with
  | Int z => Z.gtb z 0
  | Real r => if Rlt_dec 0 r then true else false
  end.

Definition get_positive_spec (l : list Num) (res : list Num) : Prop :=
  res = filter is_pos l.

Example get_positive_spec_test :
  get_positive_spec
    [Int (-3%Z); Real (0.5%R); Int (-4%Z); Real (2.5%R); Int (5%Z);
     Real (-2.2%R); Real (0.3470794389448922%R); Int (-8%Z); Int (-4%Z);
     Int (-7%Z); Real (9.9%R); Real (-10.5%R)]
    [Real (0.5%R); Real (2.5%R); Int (5%Z); Real (0.3470794389448922%R); Real (9.9%R)].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0 0.5%R); [| lra]. simpl.
  destruct (Rlt_dec 0 2.5%R); [| lra]. simpl.
  destruct (Rlt_dec 0 (-2.2%R)); [lra |]. simpl.
  destruct (Rlt_dec 0 0.3470794389448922%R); [| lra]. simpl.
  destruct (Rlt_dec 0 9.9%R); [| lra]. simpl.
  destruct (Rlt_dec 0 (-10.5%R)); [lra |]. simpl.
  reflexivity.
Qed.