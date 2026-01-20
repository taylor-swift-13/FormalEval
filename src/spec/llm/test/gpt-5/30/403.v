Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Import ListNotations.

Open Scope Z_scope.
Open Scope R_scope.

Inductive Num : Type :=
| Nz : Z -> Num
| Nr : R -> Num.

Definition positiveb (x : Num) : bool :=
  match x with
  | Nz z => Z.gtb z 0
  | Nr _ => false
  end.

Definition get_positive_spec (l : list Num) (res : list Num) : Prop :=
  res = filter positiveb l.

Example get_positive_spec_test :
  get_positive_spec
    [Nz 0%Z; Nr (-(5%R)/(4%R)); Nr (-(3%R)/(2%R)); Nr (-(3%R)/(4%R)); Nr (-(9%R)/(4%R)); Nz (-1%Z); Nz (-2%Z); Nz (-3%Z); Nz (-4%Z); Nz (-5%Z); Nz (-6%Z); Nr (-(3%R)/(4%R)); Nr (-(3%R)/(4%R))]
    [].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.