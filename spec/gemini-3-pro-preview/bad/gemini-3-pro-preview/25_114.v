Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime_bool (p : Z) : bool :=
  if p <=? 1 then false
  else 
    let fix check (d : Z) (fuel : nat) : bool :=
      match fuel with
      | O => true
      | S f => 
        if d * d >? p then true
        else if (p mod d =? 0) then false
        else check (d + 1) f
      end
    in check 2 (Z.to_nat (Z.sqrt p) + 2).

Definition is_prime (p : Z) : Prop := is_prime_bool p = true.

Definition factorize_spec (n : Z) (factors : list Z) : Prop :=
  fold_right Z.mul 1 factors = n /\
  Forall is_prime factors /\
  Sorted Z.le factors.

Example test_factorize : factorize_spec 1003000998 [2; 3; 167; 1000999].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + repeat constructor; vm_compute; reflexivity.
    + repeat constructor; try lia.
Qed.