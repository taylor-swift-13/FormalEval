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

Example test_single_positive : below_zero_spec [1%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - (* Case: result = true <-> ... *)
    split.
    + (* false = true -> ... *)
      intro H. discriminate H.
    + (* exists ... -> false = true *)
      intros [prefix [suffix [Heq Hsum]]].
      destruct prefix as [|z prefix'].
      * (* prefix = [] *)
        unfold sum_list in Hsum.
        simpl in Hsum.
        lia.
      * (* prefix = z :: prefix' *)
        simpl in Heq.
        injection Heq as Hz Hrest. subst z.
        destruct prefix' as [|z0 prefix''].
        ** (* prefix = [1] *)
           unfold sum_list in Hsum.
           simpl in Hsum.
           lia.
        ** (* prefix has > 1 elements *)
           simpl in Hrest.
           discriminate Hrest.
  - (* Case: result = false <-> ... *)
    split.
    + (* false = false -> forall ... *)
      intros _ prefix suffix Heq.
      destruct prefix as [|z prefix'].
      * (* prefix = [] *)
        unfold sum_list.
        simpl.
        lia.
      * (* prefix = z :: prefix' *)
        simpl in Heq.
        injection Heq as Hz Hrest. subst z.
        destruct prefix' as [|z0 prefix''].
        ** (* prefix = [1] *)
           unfold sum_list.
           simpl.
           lia.
        ** (* prefix has > 1 elements *)
           simpl in Hrest.
           discriminate Hrest.
    + (* forall ... -> false = false *)
      intro H. reflexivity.
Qed.