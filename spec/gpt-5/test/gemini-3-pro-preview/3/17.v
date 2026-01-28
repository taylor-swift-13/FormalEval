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

Example test_below_zero : below_zero_spec [15%Z; 2%Z; 3%Z; -6%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intro H. discriminate H.
    + intros [prefix [suffix [Heq Hsum]]].
      unfold sum_list in Hsum.
      destruct prefix as [|z0 prefix].
      * simpl in Hsum. lia.
      * destruct prefix as [|z1 prefix].
        -- simpl in Heq. inversion Heq; subst. simpl in Hsum. lia.
        -- destruct prefix as [|z2 prefix].
           ++ simpl in Heq. inversion Heq; subst. simpl in Hsum. lia.
           ++ destruct prefix as [|z3 prefix].
              ** simpl in Heq. inversion Heq; subst. simpl in Hsum. lia.
              ** destruct prefix as [|z4 prefix].
                 --- simpl in Heq. inversion Heq; subst. simpl in Hsum. lia.
                 --- simpl in Heq. discriminate Heq.
  - split.
    + intros _ prefix suffix Heq.
      unfold sum_list.
      destruct prefix as [|z0 prefix].
      * simpl. lia.
      * destruct prefix as [|z1 prefix].
        -- simpl in Heq. inversion Heq; subst. simpl. lia.
        -- destruct prefix as [|z2 prefix].
           ++ simpl in Heq. inversion Heq; subst. simpl. lia.
           ++ destruct prefix as [|z3 prefix].
              ** simpl in Heq. inversion Heq; subst. simpl. lia.
              ** destruct prefix as [|z4 prefix].
                 --- simpl in Heq. inversion Heq; subst. simpl. lia.
                 --- simpl in Heq. discriminate Heq.
    + intro H. reflexivity.
Qed.