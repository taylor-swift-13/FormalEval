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

Example test_factorize_47 : factorize_spec 47 [47].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 47 *)
        unfold is_prime. split.
        -- (* 47 > 1 *)
           lia.
        -- (* Divisors check *)
           intros d Hdiv.
           assert (Hle : d <= 47).
           { apply Nat.divide_pos_le; try lia. assumption. }
           destruct d as [|d].
           ++ (* d = 0 *)
              destruct Hdiv as [z Hz].
              simpl in Hz. discriminate.
           ++ destruct d as [|d].
              ** (* d = 1 *)
                 left. reflexivity.
              ** (* d >= 2 *)
                 apply Nat.mod_divide in Hdiv; try lia.
                 (* Check d = 2 to 46 *)
                 do 45 (destruct d as [|d]; [ simpl in Hdiv; discriminate | ]).
                 (* d = 47 *)
                 right.
                 destruct d as [|d].
                 --- reflexivity.
                 --- exfalso. lia.
      * (* End of list *)
        constructor.
    + (* Part 3: Sorted check *)
      repeat constructor.
Qed.