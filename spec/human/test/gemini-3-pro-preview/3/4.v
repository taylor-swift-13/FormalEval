Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_new: problem_3_spec [1%Z; -1%Z; 2%Z; -2%Z; 5%Z; -5%Z; 4%Z; -4%Z] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [H Hlt]]].
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in H; injection H as H1 H; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in H; injection H as H1 H; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in H; injection H as H1 H; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in H; injection H as H1 H; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in H; injection H as H1 H; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in H; injection H as H1 H; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in H; injection H as H1 H; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in H; injection H as H1 H; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in H; discriminate.
  - intros H; discriminate.
Qed.