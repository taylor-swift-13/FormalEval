Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_left Z.add l 0%Z.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  (result = true <-> exists prefix suffix, operations = prefix ++ suffix /\ sum_list prefix < 0%Z) /\
  (result = false <-> forall prefix suffix, operations = prefix ++ suffix -> 0%Z <= sum_list prefix).

Example test_balance : below_zero_spec [1000000%Z; -500000%Z; -500000%Z; 1000000%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intro H. discriminate H.
    + intros [prefix [suffix [Heq Hsum]]].
      destruct prefix as [|z1 p1].
      * unfold sum_list in Hsum. simpl in Hsum. lia.
      * destruct p1 as [|z2 p2].
        -- inversion Heq; subst. unfold sum_list in Hsum. simpl in Hsum. lia.
        -- destruct p2 as [|z3 p3].
           ++ inversion Heq; subst. unfold sum_list in Hsum. simpl in Hsum. lia.
           ++ destruct p3 as [|z4 p4].
              ** inversion Heq; subst. unfold sum_list in Hsum. simpl in Hsum. lia.
              ** destruct p4 as [|z5 p5].
                 --- inversion Heq; subst. unfold sum_list in Hsum. simpl in Hsum. lia.
                 --- inversion Heq.
  - split.
    + intros _ prefix suffix Heq.
      destruct prefix as [|z1 p1].
      * unfold sum_list. simpl. lia.
      * destruct p1 as [|z2 p2].
        -- inversion Heq; subst. unfold sum_list. simpl. lia.
        -- destruct p2 as [|z3 p3].
           ++ inversion Heq; subst. unfold sum_list. simpl. lia.
           ++ destruct p3 as [|z4 p4].
              ** inversion Heq; subst. unfold sum_list. simpl. lia.
              ** destruct p4 as [|z5 p5].
                 --- inversion Heq; subst. unfold sum_list. simpl. lia.
                 --- inversion Heq.
    + intro H. reflexivity.
Qed.