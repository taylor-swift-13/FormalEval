Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example problem_3_test_nonneg : problem_3_spec [0%Z; 35%Z] false.
Proof.
  unfold problem_3_spec; simpl.
  split.
  - intros [prefix [suffix [Happ Hlt]]].
    destruct prefix as [|z1 prefix1].
    + simpl in Happ. subst suffix.
      simpl in Hlt. lia.
    + simpl in Happ. inversion Happ; subst.
      destruct prefix1 as [|z2 prefix2].
      * simpl in H1. subst. simpl in Hlt. lia.
      * simpl in H1. inversion H1; subst.
        apply app_eq_nil in H2. destruct H2 as [Hp2 Hsuf]. subst. simpl in Hlt. lia.
  - intros Hfalse. exfalso. discriminate.
Qed.