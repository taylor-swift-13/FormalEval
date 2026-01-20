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

Example test_factorize_13 : factorize_spec 13 [13].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           destruct d as [|d].
           { destruct Hdiv as [x Hx]. simpl in Hx. discriminate. }
           destruct d as [|d].
           { left. reflexivity. }
           right.
           apply Nat.mod_divide in Hdiv; [| lia].
           destruct d as [|d]; [ simpl in Hdiv; discriminate | ]. (* 2 *)
           destruct d as [|d]; [ simpl in Hdiv; discriminate | ]. (* 3 *)
           destruct d as [|d]; [ simpl in Hdiv; discriminate | ]. (* 4 *)
           destruct d as [|d]; [ simpl in Hdiv; discriminate | ]. (* 5 *)
           destruct d as [|d]; [ simpl in Hdiv; discriminate | ]. (* 6 *)
           destruct d as [|d]; [ simpl in Hdiv; discriminate | ]. (* 7 *)
           destruct d as [|d]; [ simpl in Hdiv; discriminate | ]. (* 8 *)
           destruct d as [|d]; [ simpl in Hdiv; discriminate | ]. (* 9 *)
           destruct d as [|d]; [ simpl in Hdiv; discriminate | ]. (* 10 *)
           destruct d as [|d]; [ simpl in Hdiv; discriminate | ]. (* 11 *)
           destruct d as [|d]; [ simpl in Hdiv; discriminate | ]. (* 12 *)
           destruct d as [|d]; [ reflexivity | ]. (* 13 *)
           simpl in Hdiv. discriminate.
      * constructor.
    + repeat constructor.
Qed.