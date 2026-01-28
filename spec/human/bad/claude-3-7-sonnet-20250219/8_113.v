Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example test_single_list_of_sixty_ones :
  problem_8_spec (repeat 1 60) 60 1.
Proof.
  unfold problem_8_spec.
  simpl.
  split.
  - (* sum = 60 *)
    unfold repeat.
    rewrite fold_left_nseq_add.
    reflexivity.
  - (* product = 1 *)
    unfold repeat.
    rewrite fold_left_nseq_mul.
    reflexivity.
Qed.

(* Supporting lemmas for sums and products over repeated lists *)
Lemma fold_left_nseq_add : forall a n init,
  fold_left Z.add (repeat a n) init = init + a * (Z.of_nat n).
Proof.
  intros a n.
  induction n as [|n' IH]; intros init.
  - simpl. lia.
  - simpl repeat.
    rewrite fold_left_app.
    simpl.
    rewrite Z.add_assoc.
    rewrite IH.
    lia.
Qed.

Lemma fold_left_nseq_mul : forall a n init,
  fold_left Z.mul (repeat a n) init = init * (a ^ (Z.of_nat n)).
Proof.
  intros a n.
  induction n as [|n' IH]; intros init.
  - simpl. lia.
  - simpl repeat.
    rewrite fold_left_app.
    simpl.
    rewrite Z.mul_assoc.
    rewrite IH.
    apply Z.pow_add_r.
Qed.