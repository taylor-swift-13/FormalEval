Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_new: problem_3_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; -15%Z; 7%Z; 8%Z; 9%Z; -19%Z; 21%Z; -19%Z] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Happ Hlt]]].
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in Happ; injection Happ as ? Happ; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in Happ; injection Happ as ? Happ; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in Happ; injection Happ as ? Happ; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in Happ; injection Happ as ? Happ; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in Happ; injection Happ as ? Happ; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in Happ; injection Happ as ? Happ; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in Happ; injection Happ as ? Happ; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in Happ; injection Happ as ? Happ; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in Happ; injection Happ as ? Happ; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in Happ; injection Happ as ? Happ; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in Happ; injection Happ as ? Happ; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in Happ; injection Happ as ? Happ; subst.
    destruct prefix; [ simpl in Hlt; lia | ].
    simpl in Happ; discriminate.
  - intros H. discriminate H.
Qed.