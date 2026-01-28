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

Example test_factorize_77 : factorize_spec 77 [7; 11].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 7 *)
        unfold is_prime. split.
        -- (* 7 > 1 *)
           lia.
        -- (* Divisors check *)
           intros d Hdiv.
           destruct d as [|d]; [apply Nat.divide_0_l in Hdiv; discriminate|].
           destruct d as [|d]; [left; reflexivity|]. (* d=1 *)
           destruct d as [|d]. (* d=2 *)
           { assert (7 mod 2 = 0) as H by (apply Nat.mod_divide; [lia|exact Hdiv]); compute in H; discriminate. }
           destruct d as [|d]. (* d=3 *)
           { assert (7 mod 3 = 0) as H by (apply Nat.mod_divide; [lia|exact Hdiv]); compute in H; discriminate. }
           destruct d as [|d]. (* d=4 *)
           { assert (7 mod 4 = 0) as H by (apply Nat.mod_divide; [lia|exact Hdiv]); compute in H; discriminate. }
           destruct d as [|d]. (* d=5 *)
           { assert (7 mod 5 = 0) as H by (apply Nat.mod_divide; [lia|exact Hdiv]); compute in H; discriminate. }
           destruct d as [|d]. (* d=6 *)
           { assert (7 mod 6 = 0) as H by (apply Nat.mod_divide; [lia|exact Hdiv]); compute in H; discriminate. }
           destruct d as [|d]. (* d=7 *)
           { right; reflexivity. }
           (* d >= 8 *)
           apply Nat.divide_pos_le in Hdiv; [|lia]. lia.
      * constructor.
        -- (* is_prime 11 *)
           unfold is_prime. split.
           ++ (* 11 > 1 *)
              lia.
           ++ (* Divisors check *)
              intros d Hdiv.
              destruct d as [|d]; [apply Nat.divide_0_l in Hdiv; discriminate|].
              destruct d as [|d]; [left; reflexivity|]. (* d=1 *)
              destruct d as [|d]. (* d=2 *)
              { assert (11 mod 2 = 0) as H by (apply Nat.mod_divide; [lia|exact Hdiv]); compute in H; discriminate. }
              destruct d as [|d]. (* d=3 *)
              { assert (11 mod 3 = 0) as H by (apply Nat.mod_divide; [lia|exact Hdiv]); compute in H; discriminate. }
              destruct d as [|d]. (* d=4 *)
              { assert (11 mod 4 = 0) as H by (apply Nat.mod_divide; [lia|exact Hdiv]); compute in H; discriminate. }
              destruct d as [|d]. (* d=5 *)
              { assert (11 mod 5 = 0) as H by (apply Nat.mod_divide; [lia|exact Hdiv]); compute in H; discriminate. }
              destruct d as [|d]. (* d=6 *)
              { assert (11 mod 6 = 0) as H by (apply Nat.mod_divide; [lia|exact Hdiv]); compute in H; discriminate. }
              destruct d as [|d]. (* d=7 *)
              { assert (11 mod 7 = 0) as H by (apply Nat.mod_divide; [lia|exact Hdiv]); compute in H; discriminate. }
              destruct d as [|d]. (* d=8 *)
              { assert (11 mod 8 = 0) as H by (apply Nat.mod_divide; [lia|exact Hdiv]); compute in H; discriminate. }
              destruct d as [|d]. (* d=9 *)
              { assert (11 mod 9 = 0) as H by (apply Nat.mod_divide; [lia|exact Hdiv]); compute in H; discriminate. }
              destruct d as [|d]. (* d=10 *)
              { assert (11 mod 10 = 0) as H by (apply Nat.mod_divide; [lia|exact Hdiv]); compute in H; discriminate. }
              destruct d as [|d]. (* d=11 *)
              { right; reflexivity. }
              (* d >= 12 *)
              apply Nat.divide_pos_le in Hdiv; [|lia]. lia.
        -- (* End of list *)
           constructor.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.