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

Example test_factorize_33 : factorize_spec 33 [3; 11].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 3 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           destruct d as [|d]; [destruct Hdiv as [k Hk]; simpl in Hk; discriminate|].
           destruct d as [|d]; [left; reflexivity|].
           destruct d as [|d]; [destruct Hdiv as [k Hk]; simpl in Hk; lia|].
           destruct d as [|d]; [right; reflexivity|].
           apply Nat.divide_pos_le in Hdiv; lia.
      * constructor.
        -- (* is_prime 11 *)
           unfold is_prime. split.
           ++ lia.
           ++ intros d Hdiv.
              destruct d as [|d]; [destruct Hdiv as [k Hk]; simpl in Hk; discriminate|]. (* d=0 *)
              destruct d as [|d]; [left; reflexivity|]. (* d=1 *)
              destruct d as [|d]; [destruct Hdiv as [k Hk]; simpl in Hk; lia|]. (* d=2 *)
              destruct d as [|d]; [destruct Hdiv as [k Hk]; simpl in Hk; lia|]. (* d=3 *)
              destruct d as [|d]; [destruct Hdiv as [k Hk]; simpl in Hk; lia|]. (* d=4 *)
              destruct d as [|d]; [destruct Hdiv as [k Hk]; simpl in Hk; lia|]. (* d=5 *)
              destruct d as [|d]; [destruct Hdiv as [k Hk]; simpl in Hk; lia|]. (* d=6 *)
              destruct d as [|d]; [destruct Hdiv as [k Hk]; simpl in Hk; lia|]. (* d=7 *)
              destruct d as [|d]; [destruct Hdiv as [k Hk]; simpl in Hk; lia|]. (* d=8 *)
              destruct d as [|d]; [destruct Hdiv as [k Hk]; simpl in Hk; lia|]. (* d=9 *)
              destruct d as [|d]; [destruct Hdiv as [k Hk]; simpl in Hk; lia|]. (* d=10 *)
              destruct d as [|d]; [right; reflexivity|]. (* d=11 *)
              apply Nat.divide_pos_le in Hdiv; lia. (* d >= 12 *)
        -- constructor.
    + (* Part 3: Sorted check *)
      repeat constructor.
Qed.