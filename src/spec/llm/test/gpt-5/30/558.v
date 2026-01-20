Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope Z_scope.
Open Scope R_scope.

Inductive num := NumZ (z : Z) | NumR (r : R).

Definition Rgtb (x y : R) : bool :=
  if Rlt_dec y x then true else false.

Definition is_positive (n : num) : bool :=
  match n with
  | NumZ z => Z.gtb z 0
  | NumR r => Rgtb r 0
  end.

Definition get_positive_spec (l : list num) (res : list num) : Prop :=
  res = filter is_positive l.

Lemma Rgtb_true : forall x y, x > y -> Rgtb x y = true.
Proof.
  intros x y H.
  unfold Rgtb.
  destruct (Rlt_dec y x) as [Hyx|Hyx]; [reflexivity|].
  exfalso; lra.
Qed.

Lemma Rgtb_false : forall x y, ~ x > y -> Rgtb x y = false.
Proof.
  intros x y H.
  unfold Rgtb.
  destruct (Rlt_dec y x) as [Hyx|Hyx]; [exfalso; lra|reflexivity].
Qed.

Example get_positive_spec_test :
  get_positive_spec
    [NumR 0.5%R; NumZ 0%Z; NumR 2.5%R; NumZ 5%Z; NumR (-2.2)%R; NumZ (-8)%Z; NumR (-0.75)%R; NumR 7.7%R; NumR 9.9%R; NumR (-10.5)%R; NumZ 5%Z; NumZ (-8)%Z]
    [NumR 0.5%R; NumR 2.5%R; NumZ 5%Z; NumR 7.7%R; NumR 9.9%R; NumZ 5%Z].
Proof.
  unfold get_positive_spec.
  simpl.
  rewrite (Rgtb_true 0.5%R 0%R); [simpl|lra].
  rewrite (Rgtb_true 2.5%R 0%R); [simpl|lra].
  rewrite (Rgtb_false (-2.2)%R 0%R); [simpl|lra].
  rewrite (Rgtb_false (-0.75)%R 0%R); [simpl|lra].
  rewrite (Rgtb_true 7.7%R 0%R); [simpl|lra].
  rewrite (Rgtb_true 9.9%R 0%R); [simpl|lra].
  rewrite (Rgtb_false (-10.5)%R 0%R); [simpl|lra].
  reflexivity.
Qed.