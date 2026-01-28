Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* We define a boolean primality check to handle large numbers efficiently in proofs *)
Fixpoint check_divs (d : nat) (fuel : nat) (n : Z) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
    let z_d := Z.of_nat d in
    if (z_d * z_d >? n)%Z then true
    else if (Z.rem n z_d =? 0)%Z then false
    else check_divs (S d) fuel' n
  end.

Definition is_prime_bool (n : Z) : bool :=
  if (n <=? 1)%Z then false
  else check_divs 2 (Z.to_nat (Z.sqrt n) + 2) n.

Definition is_prime (p : Z) : Prop :=
  is_prime_bool p = true.

Definition factorize_spec (n : Z) (factors : list Z) : Prop :=
  fold_right Z.mul 1 factors = n /\
  Forall is_prime factors /\
  Sorted Z.le factors.

Example test_factorize_new : factorize_spec 9999999969 [3; 3333333323].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    vm_compute. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 3 *)
        unfold is_prime. vm_compute. reflexivity.
      * constructor.
        -- (* is_prime 3333333323 *)
           unfold is_prime. vm_compute. reflexivity.
        -- constructor.
    + (* Part 3: Sorted check *)
      repeat constructor.
      simpl. lia.
Qed.