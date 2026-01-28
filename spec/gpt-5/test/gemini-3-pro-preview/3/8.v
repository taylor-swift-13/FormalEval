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

Example test_zeros : below_zero_spec [0%Z; 0%Z; 0%Z; 0%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - (* Case: result = true <-> ... *)
    split.
    + (* false = true -> ... *)
      intro H. discriminate H.
    + (* exists ... -> false = true *)
      intros [prefix [suffix [Heq Hsum]]].
      destruct prefix as [|z1 [|z2 [|z3 [|z4 [|z5 prefix']]]]].
      * (* prefix = [] *)
        unfold sum_list in Hsum. simpl in Hsum. lia.
      * (* prefix = [z1] *)
        simpl in Heq. injection Heq as Hz1 Htl. subst.
        unfold sum_list in Hsum. simpl in Hsum. lia.
      * (* prefix = [z1; z2] *)
        simpl in Heq. injection Heq as Hz1 Hz2 Htl. subst.
        unfold sum_list in Hsum. simpl in Hsum. lia.
      * (* prefix = [z1; z2; z3] *)
        simpl in Heq. injection Heq as Hz1 Hz2 Hz3 Htl. subst.
        unfold sum_list in Hsum. simpl in Hsum. lia.
      * (* prefix = [z1; z2; z3; z4] *)
        simpl in Heq. injection Heq as Hz1 Hz2 Hz3 Hz4 Htl. subst.
        unfold sum_list in Hsum. simpl in Hsum. lia.
      * (* prefix too long *)
        simpl in Heq. discriminate Heq.
  - (* Case: result = false <-> ... *)
    split.
    + (* false = false -> forall ... *)
      intros _ prefix suffix Heq.
      destruct prefix as [|z1 [|z2 [|z3 [|z4 [|z5 prefix']]]]].
      * (* prefix = [] *)
        unfold sum_list. simpl. lia.
      * (* prefix = [z1] *)
        simpl in Heq. injection Heq as Hz1 Htl. subst.
        unfold sum_list. simpl. lia.
      * (* prefix = [z1; z2] *)
        simpl in Heq. injection Heq as Hz1 Hz2 Htl. subst.
        unfold sum_list. simpl. lia.
      * (* prefix = [z1; z2; z3] *)
        simpl in Heq. injection Heq as Hz1 Hz2 Hz3 Htl. subst.
        unfold sum_list. simpl. lia.
      * (* prefix = [z1; z2; z3; z4] *)
        simpl in Heq. injection Heq as Hz1 Hz2 Hz3 Hz4 Htl. subst.
        unfold sum_list. simpl. lia.
      * (* prefix too long *)
        simpl in Heq. discriminate Heq.
    + (* forall ... -> false = false *)
      intro H. reflexivity.
Qed.