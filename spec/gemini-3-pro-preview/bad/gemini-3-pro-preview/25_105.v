Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  p > 1 /\ forall d : Z, 1 < d < p -> ~ (d | p).

Definition factorize_spec (n : Z) (factors : list Z) : Prop :=
  fold_right Z.mul 1 factors = n /\
  Forall is_prime factors /\
  Sorted Z.le factors.

Fixpoint check_range (n d : Z) (count : nat) : bool :=
  match count with
  | O => true
  | S c => if Z.rem n d =? 0 then false else check_range n (d + 1) c
  end.

Lemma check_range_correct : forall n d c, 
  check_range n d c = true -> 
  forall k, d <= k < d + Z.of_nat c -> ~ (k | n).
Proof.
  induction c; intros; simpl in *.
  - lia.
  - destruct (Z.rem n d =? 0) eqn:Heq.
    + discriminate.
    + apply Z.eqb_neq in Heq.
      destruct (Z.eq_dec k d).
      * subst. intro Hdiv. apply Z.rem_divide in Hdiv; [|lia]. contradiction.
      * apply IHc; auto. lia.
Qed.

Lemma is_prime_vm : forall p, 
  p > 1 -> 
  check_range p 2 (Z.to_nat (p - 2)) = true -> 
  is_prime p.
Proof.
  intros p Hp Hchk. split; auto.
  intros d Hrange.
  apply (check_range_correct p 2 (Z.to_nat (p - 2))); auto.
  lia.
Qed.

Example test_factorize_2147483644 : factorize_spec 2147483644 [2; 2; 233; 1103; 2089].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + repeat (constructor; [ apply is_prime_vm; [lia | vm_compute; reflexivity] | ]).
      apply Forall_nil.
    + repeat constructor; lia.
Qed.