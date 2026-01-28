Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example problem_3_test_case : problem_3_spec [10%Z; 30%Z; -40%Z; 50%Z; 6%Z] false.
Proof.
  unfold problem_3_spec; simpl.
  split.
  - intros [prefix [suffix [Happ Hlt]]].
    exfalso.
    destruct prefix as [|a prefix1].
    + simpl in Happ. subst suffix. simpl in Hlt. lia.
    + simpl in Happ. inversion Happ; subst.
      destruct prefix1 as [|b prefix2].
      * simpl in H1. subst suffix. simpl in Hlt. lia.
      * simpl in H1. inversion H1; subst.
        destruct prefix2 as [|c prefix3].
        { simpl in H2. subst suffix. simpl in Hlt. lia. }
        { simpl in H2. inversion H2; subst.
          destruct prefix3 as [|d prefix4].
          - simpl in H3. subst suffix. simpl in Hlt. lia.
          - simpl in H3. inversion H3; subst.
            destruct prefix4 as [|e prefix5].
            + simpl in H4. subst suffix. simpl in Hlt. lia.
            + simpl in H4. inversion H4; subst.
              destruct prefix5 as [|f prefix6].
              * simpl in H5. subst suffix. simpl in Hlt. lia.
              * simpl in H5. inversion H5.
        }
  - intros Hfalse. exfalso. discriminate.
Qed.