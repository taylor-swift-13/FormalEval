Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example problem_3_test_13 : problem_3_spec [1%Z; 3%Z] false.
Proof.
  unfold problem_3_spec; simpl.
  split.
  - intros [prefix [suffix [Happ Hlt]]].
    destruct prefix as [|p1 prefix1].
    + simpl in Happ. subst suffix.
      simpl in Hlt. exfalso. lia.
    + destruct prefix1 as [|p2 prefix2].
      * simpl in Happ. inversion Happ. subst p1. subst suffix.
        simpl in Hlt. exfalso. lia.
      * simpl in Happ. inversion Happ as [Hp1 Hrest]. subst p1.
        inversion Hrest as [Hp2 Hnil]. subst p2.
        apply app_eq_nil in Hnil. destruct Hnil as [Hprefix2 Hsuffix].
        subst prefix2. subst suffix.
        simpl in Hlt. exfalso. lia.
  - intros Hfalse. exfalso. discriminate.
Qed.