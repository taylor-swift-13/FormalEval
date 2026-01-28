Require Import Arith.
Require Import List.
Require Import Lia.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Fixpoint is_prime (n : nat) : bool :=
  match n with
  | 0 | 1 => false
  | _ => forallb (fun d => negb (n mod d =? 0)) (seq 2 (n - 2))
  end.

Lemma seq_correct : forall n d, In d (seq 2 (n - 2)) -> 2 <= d < n.
Proof.
  intros n d H.
  apply In_seq in H.
  lia.
Qed.

Example test_is_prime_6 :
  problem_31_spec 6 (is_prime 6).
Proof.
  unfold problem_31_spec.
  simpl.
  split.
  - intros [H1 H2].
    assert (H3: 6 mod 2 = 0) by reflexivity.
    specialize (H2 2 H3).
    destruct H2 as [H2 | H2].
    + lia.
    + lia.
  - intros H.
    simpl in H.
    apply Bool.forallb_false in H.
    destruct H as [x [H4 H5]].
    apply negb_true_iff in H5.
    apply Nat.eqb_eq in H5.
    apply seq_correct in H4.
    lia.
Qed.