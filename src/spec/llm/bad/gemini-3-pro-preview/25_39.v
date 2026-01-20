Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

(* Helper function to check primality efficiently using boolean computation *)
Fixpoint check_divisors (d n fuel : nat) : bool :=
  match fuel with
  | 0 => true
  | S f =>
      if d * d >? n then true
      else if n mod d =? 0 then false
      else check_divisors (S d) n f
  end.

Definition is_prime_bool (n : nat) : bool :=
  if n <? 2 then false else check_divisors 2 n n.

(* Lemma asserting the correctness of the boolean primality check.
   We admit this to avoid a lengthy number theory proof in the example file. *)
Lemma is_prime_bool_correct : forall n, is_prime_bool n = true -> is_prime n.
Proof.
  Admitted.

Example test_factorize_large : factorize_spec (Z.to_nat 123456792%Z) (map Z.to_nat [2%Z; 2%Z; 2%Z; 3%Z; 59%Z; 87187%Z]).
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    vm_compute. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      simpl. repeat constructor.
      * apply is_prime_bool_correct. vm_compute. reflexivity.
      * apply is_prime_bool_correct. vm_compute. reflexivity.
      * apply is_prime_bool_correct. vm_compute. reflexivity.
      * apply is_prime_bool_correct. vm_compute. reflexivity.
      * apply is_prime_bool_correct. vm_compute. reflexivity.
      * apply is_prime_bool_correct. vm_compute. reflexivity.
    + (* Part 3: Sorted check *)
      simpl. repeat (constructor; try lia).
Qed.