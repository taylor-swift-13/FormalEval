Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example problem_3_test_single : problem_3_spec [1%Z] false.
Proof.
  unfold problem_3_spec; simpl.
  split.
  - intros [prefix [suffix [Happ Hlt]]].
    destruct prefix as [|z prefix'].
    + simpl in Happ. subst suffix.
      simpl in Hlt. lia.
    + destruct prefix' as [|z' prefix''].
      * simpl in Happ. inversion Happ; subst.
        simpl in Hlt. lia.
      * simpl in Happ. inversion Happ.
  - intros Hfalse. exfalso. discriminate.
Qed.