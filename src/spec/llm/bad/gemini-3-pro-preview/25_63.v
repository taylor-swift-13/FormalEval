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

Example test_factorize_78 : factorize_spec 78 [2; 3; 13].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      repeat constructor.
      * (* is_prime 2 *)
        unfold is_prime. split. lia.
        intros d Hdiv.
        apply Nat.divide_pos_le in Hdiv; [|lia].
        destruct d as [|d]; [destruct Hdiv as [x Hx]; simpl in Hx; lia|].
        destruct d as [|d]; [left; reflexivity|].
        destruct d as [|d]; [right; reflexivity|].
        lia.
      * (* is_prime 3 *)
        unfold is_prime. split. lia.
        intros d Hdiv.
        apply Nat.divide_pos_le in Hdiv; [|lia].
        destruct d as [|d]; [destruct Hdiv as [x Hx]; simpl in Hx; lia|].
        destruct d as [|d]; [left; reflexivity|].
        destruct d as [|d]; [destruct Hdiv as [k Hk]; simpl in Hk; lia|].
        destruct d as [|d]; [right; reflexivity|].
        lia.
      * (* is_prime 13 *)
        unfold is_prime. split. lia.
        intros d Hdiv.
        apply Nat.divide_pos_le in Hdiv; [|lia].
        (* d=0 *) destruct d as [|d]; [destruct Hdiv as [x Hx]; simpl in Hx; lia|].
        (* d=1 *) destruct d as [|d]; [left; reflexivity|].
        (* d=2..12 *)
        do 11 (destruct d as [|d]; [destruct Hdiv as [k Hk]; simpl in Hk; lia|]).
        (* d=13 *) destruct d as [|d]; [right; reflexivity|].
        (* d>13 *) lia.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.