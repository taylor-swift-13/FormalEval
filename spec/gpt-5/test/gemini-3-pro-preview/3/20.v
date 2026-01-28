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

Example test_simple_pos : below_zero_spec [1%Z; 3%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - (* Case: result = true <-> ... *)
    split.
    + (* false = true -> ... *)
      intro H. discriminate H.
    + (* exists ... -> false = true *)
      intros [prefix [suffix [Heq Hsum]]].
      destruct prefix as [|z1 prefix'].
      * (* prefix = [] *)
        unfold sum_list in Hsum. simpl in Hsum. lia.
      * (* prefix = z1 :: prefix' *)
        simpl in Heq. injection Heq as Hz1 Heq1. subst z1.
        destruct prefix' as [|z2 prefix''].
        -- (* prefix = [1] *)
           unfold sum_list in Hsum. simpl in Hsum. lia.
        -- (* prefix = 1 :: z2 :: prefix'' *)
           simpl in Heq1. injection Heq1 as Hz2 Heq2. subst z2.
           destruct prefix'' as [|z3 prefix'''].
           ++ (* prefix = [1; 3] *)
              unfold sum_list in Hsum. simpl in Hsum. lia.
           ++ (* prefix too long *)
              simpl in Heq2. discriminate Heq2.
  - (* Case: result = false <-> ... *)
    split.
    + (* false = false -> forall ... *)
      intros _ prefix suffix Heq.
      destruct prefix as [|z1 prefix'].
      * (* prefix = [] *)
        unfold sum_list. simpl. lia.
      * (* prefix = z1 :: prefix' *)
        simpl in Heq. injection Heq as Hz1 Heq1. subst z1.
        destruct prefix' as [|z2 prefix''].
        -- (* prefix = [1] *)
           unfold sum_list. simpl. lia.
        -- (* prefix = 1 :: z2 :: prefix'' *)
           simpl in Heq1. injection Heq1 as Hz2 Heq2. subst z2.
           destruct prefix'' as [|z3 prefix'''].
           ++ (* prefix = [1; 3] *)
              unfold sum_list. simpl. lia.
           ++ (* prefix too long *)
              simpl in Heq2. discriminate Heq2.
    + (* forall ... -> false = false *)
      intro H. reflexivity.
Qed.