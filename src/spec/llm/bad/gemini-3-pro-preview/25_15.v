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

Ltac prove_prime_2 :=
  unfold is_prime; split; [lia |
    let d := fresh "d" in
    let Hdiv := fresh "Hdiv" in
    intros d Hdiv;
    apply Nat.divide_pos_le in Hdiv; try lia;
    destruct d as [| [| [| ]]]; try lia;
    [ destruct Hdiv as [? Hz]; simpl in Hz; discriminate
    | left; reflexivity
    | right; reflexivity ]
  ].

Ltac prove_prime_5 :=
  unfold is_prime; split; [lia |
    let d := fresh "d" in
    let Hdiv := fresh "Hdiv" in
    intros d Hdiv;
    apply Nat.divide_pos_le in Hdiv; try lia;
    destruct d as [| [| [| [| [| [| ]]]]]]; try lia;
    [ destruct Hdiv as [? Hz]; simpl in Hz; discriminate
    | left; reflexivity
    | exfalso; destruct Hdiv as [k Hk]; destruct k as [| [| [| ]]]; simpl in Hk; try lia
    | exfalso; destruct Hdiv as [k Hk]; destruct k as [| [| ]]; simpl in Hk; try lia
    | exfalso; destruct Hdiv as [k Hk]; destruct k as [| [| ]]; simpl in Hk; try lia
    | right; reflexivity ]
  ].

Example test_factorize_1000 : factorize_spec 1000 [2; 2; 2; 5; 5; 5].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + repeat constructor.
      * prove_prime_2.
      * prove_prime_2.
      * prove_prime_2.
      * prove_prime_5.
      * prove_prime_5.
      * prove_prime_5.
    + repeat constructor; lia.
Qed.