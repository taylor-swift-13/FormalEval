Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_25_pre (input : nat) : Prop := True.

Definition problem_25_spec (input : nat) (output : list nat) : Prop :=
  Sorted le output /\
  fold_right Nat.mul 1 output = input /\
  Forall IsPrime output.

Lemma two_is_prime : IsPrime 2.
Proof.
  unfold IsPrime.
  split.
  - auto with arith.
  - intros d Hmod.
    destruct d as [|[|[|d']]].
    + simpl in Hmod. discriminate.
    + left. reflexivity.
    + right. reflexivity.
    + simpl in Hmod.
      destruct d' as [|[|d'']].
      * simpl in Hmod. discriminate.
      * simpl in Hmod. discriminate.
      * simpl in Hmod. discriminate.
Qed.

Example problem_25_test_1 : problem_25_spec 2 [2].
Proof.
  unfold problem_25_spec.
  split; [| split].
  - (* Sorted le [2] *)
    apply Sorted_cons.
    + apply Sorted_nil.
    + apply HdRel_nil.
  - (* fold_right Nat.mul 1 [2] = 2 *)
    simpl. reflexivity.
  - (* Forall IsPrime [2] *)
    apply Forall_cons.
    + exact two_is_prime.
    + apply Forall_nil.
Qed.