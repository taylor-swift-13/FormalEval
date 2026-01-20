Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope Z_scope.
Open Scope R_scope.

Inductive num :=
| ZV : Z -> num
| RV : R -> num.

Definition get_positive_spec (l : list num) (res : list num) : Prop :=
  res = filter (fun x =>
    match x with
    | ZV z => Z.gtb z 0
    | RV r => if Rgt_dec r 0 then true else false
    end) l.

Example get_positive_spec_test :
  get_positive_spec
    [ZV 0%Z; RV (-1.25%R); RV (-1.5%R); RV (-0.75%R); RV (9.9%R); RV (-2.25%R);
     ZV (-1%Z); ZV (-2%Z); ZV (-3%Z); ZV (-4%Z); ZV (-5%Z); ZV 7%Z; ZV 0%Z]
    [RV 9.9%R; ZV 7%Z].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec (-1.25%R) 0%R); [lra|].
  destruct (Rgt_dec (-1.5%R) 0%R); [lra|].
  destruct (Rgt_dec (-0.75%R) 0%R); [lra|].
  destruct (Rgt_dec (9.9%R) 0%R); [|lra].
  destruct (Rgt_dec (-2.25%R) 0%R); [lra|].
  simpl.
  reflexivity.
Qed.