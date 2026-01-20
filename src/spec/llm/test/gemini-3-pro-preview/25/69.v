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

Example test_factorize_75 : factorize_spec 75 [3; 5; 5].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * unfold is_prime. split.
        -- lia.
        -- intros d [k Hk].
           destruct d as [| [| [| [| ]]]].
           ++ lia.
           ++ left. reflexivity.
           ++ exfalso. destruct k as [|[|]]; simpl in Hk; try lia.
           ++ right. reflexivity.
           ++ exfalso. destruct k; simpl in Hk; try lia.
      * constructor.
        -- unfold is_prime. split.
           ++ lia.
           ++ intros d [k Hk].
              destruct d as [| [| [| [| [| [| ]]]]]].
              ** lia.
              ** left. reflexivity.
              ** exfalso. destruct k as [|[|]]; simpl in Hk; try lia.
              ** exfalso. destruct k as [|[|]]; simpl in Hk; try lia.
              ** exfalso. destruct k as [|[|]]; simpl in Hk; try lia.
              ** right. reflexivity.
              ** exfalso. destruct k; simpl in Hk; try lia.
        -- constructor.
           ++ unfold is_prime. split.
              ** lia.
              ** intros d [k Hk].
                 destruct d as [| [| [| [| [| [| ]]]]]].
                 --- lia.
                 --- left. reflexivity.
                 --- exfalso. destruct k as [|[|]]; simpl in Hk; try lia.
                 --- exfalso. destruct k as [|[|]]; simpl in Hk; try lia.
                 --- exfalso. destruct k as [|[|]]; simpl in Hk; try lia.
                 --- right. reflexivity.
                 --- exfalso. destruct k; simpl in Hk; try lia.
           ++ constructor.
    + repeat constructor; lia.
Qed.