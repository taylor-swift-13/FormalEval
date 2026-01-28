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

Example test_positive_list : below_zero_spec [30; 1; 1; 1] false.
Proof.
  unfold below_zero_spec.
  split.
  - (* Case: result = true <-> ... *)
    split.
    + (* false = true -> ... *)
      intro H. discriminate H.
    + (* exists ... -> false = true *)
      intros [prefix [suffix [Heq Hsum]]].
      destruct prefix as [|z1 prefix].
      * (* prefix = [] *)
        unfold sum_list in Hsum. simpl in Hsum. lia.
      * destruct prefix as [|z2 prefix].
        { (* prefix = [z1] *)
          simpl in Heq. injection Heq as E1 E2. subst.
          unfold sum_list in Hsum. simpl in Hsum. lia. }
        destruct prefix as [|z3 prefix].
        { (* prefix = [z1; z2] *)
          simpl in Heq. injection Heq as E1 E2 E3. subst.
          unfold sum_list in Hsum. simpl in Hsum. lia. }
        destruct prefix as [|z4 prefix].
        { (* prefix = [z1; z2; z3] *)
          simpl in Heq. injection Heq as E1 E2 E3 E4. subst.
          unfold sum_list in Hsum. simpl in Hsum. lia. }
        destruct prefix as [|z5 prefix].
        { (* prefix = [z1; z2; z3; z4] *)
          simpl in Heq. injection Heq as E1 E2 E3 E4 E5. subst.
          unfold sum_list in Hsum. simpl in Hsum. lia. }
        { (* prefix has >= 5 elements *)
          simpl in Heq. discriminate Heq. }
  - (* Case: result = false <-> ... *)
    split.
    + (* false = false -> forall ... *)
      intros _ prefix suffix Heq.
      destruct prefix as [|z1 prefix].
      * (* prefix = [] *)
        unfold sum_list. simpl. lia.
      * destruct prefix as [|z2 prefix].
        { (* prefix = [z1] *)
          simpl in Heq. injection Heq as E1. subst.
          unfold sum_list. simpl. lia. }
        destruct prefix as [|z3 prefix].
        { (* prefix = [z1; z2] *)
          simpl in Heq. injection Heq as E1 E2. subst.
          unfold sum_list. simpl. lia. }
        destruct prefix as [|z4 prefix].
        { (* prefix = [z1; z2; z3] *)
          simpl in Heq. injection Heq as E1 E2 E3. subst.
          unfold sum_list. simpl. lia. }
        destruct prefix as [|z5 prefix].
        { (* prefix = [z1; z2; z3; z4] *)
          simpl in Heq. injection Heq as E1 E2 E3 E4. subst.
          unfold sum_list. simpl. lia. }
        { (* prefix has >= 5 elements *)
          simpl in Heq. discriminate Heq. }
    + (* forall ... -> false = false *)
      intro H. reflexivity.
Qed.