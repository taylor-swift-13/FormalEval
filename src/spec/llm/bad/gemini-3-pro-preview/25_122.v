Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

(* Helper function to check for divisors in a range *)
Fixpoint check_range (n d c : nat) : bool :=
  match c with
  | 0 => true
  | S c' => 
    if Nat.eqb (n mod d) 0 then false
    else check_range n (S d) c'
  end.

(* Correctness lemma for check_range *)
Lemma check_range_correct : forall n d c,
  d > 0 ->
  check_range n d c = true ->
  forall k, d <= k < d + c -> ~ Nat.divide k n.
Proof.
  induction c as [|c IH].
  - intros _ _ k Hk. lia.
  - intros Hd0 H k Hk.
    simpl in H.
    destruct (Nat.eqb_spec (n mod d) 0) as [Hdiv|Hnodiv].
    + discriminate H.
    + apply IH in H; [|lia].
      assert (k = d \/ k > d) as [Heq|Hgt] by lia.
      * subst k. intros Hcontr. apply Nat.mod_divide in Hcontr; [|assumption].
        lia.
      * apply H. lia.
Qed.

(* Boolean primality check *)
Definition is_prime_bool (n : nat) : bool :=
  if n <=? 1 then false
  else check_range n 2 (n - 2).

(* Correctness lemma for is_prime_bool *)
Lemma is_prime_bool_correct : forall n, is_prime_bool n = true -> is_prime n.
Proof.
  intros n H.
  unfold is_prime_bool in H.
  destruct (n <=? 1) eqn:Hle.
  - discriminate.
  - apply Nat.leb_gt in Hle.
    split; [lia|].
    intros d Hd.
    destruct (Nat.eq_dec d 1); [left; auto|].
    destruct (Nat.eq_dec d n); [right; auto|].
    exfalso.
    assert (2 <= d < 2 + (n - 2)) by lia.
    eapply check_range_correct in H; eauto.
    lia.
Qed.

Example test_factorize_999981 : factorize_spec 999981 [3; 3; 111109].
Proof.
  unfold factorize_spec.
  split.
  - (* Product check *)
    vm_compute. reflexivity.
  - split.
    + (* Primality check *)
      repeat constructor; apply is_prime_bool_correct; vm_compute; reflexivity.
    + (* Sorted check *)
      repeat constructor; lia.
Qed.