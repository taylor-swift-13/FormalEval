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

Ltac solve_not_div_23 :=
  match goal with
  | H : Nat.divide ?d 23 |- _ =>
    apply Nat.mod_divide in H; [ simpl in H; discriminate | lia ]
  end.

Example test_factorize_46 : factorize_spec 46 [2; 23].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           destruct d as [| [| [| d'] ]].
           ++ destruct Hdiv as [z Hz]. rewrite Nat.mul_0_r in Hz. discriminate.
           ++ left. reflexivity.
           ++ right. reflexivity.
           ++ apply Nat.divide_pos_le in Hdiv; try lia.
      * constructor.
        -- unfold is_prime. split.
           ++ lia.
           ++ intros d Hdiv.
              assert (Hle: d <= 23). { apply Nat.divide_pos_le in Hdiv; lia. }
              destruct d as [|d]. { destruct Hdiv; lia. }
              destruct d as [|d]. { left. reflexivity. }
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]; [ solve_not_div_23 | ].
              destruct d as [|d]. { right. reflexivity. }
              exfalso. lia.
        -- constructor.
    + repeat (constructor; try lia).
Qed.