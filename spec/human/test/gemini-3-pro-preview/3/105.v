Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1_2: problem_3_spec [1%Z; 2%Z] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Happ Hlt]]].
    destruct prefix as [|p1 [|p2 [|p3 pre_rest]]].
    + simpl in Hlt. lia.
    + simpl in Happ. injection Happ as Hp1 _. subst p1.
      simpl in Hlt. lia.
    + simpl in Happ. injection Happ as Hp1 Hp2 _. subst p1 p2.
      simpl in Hlt. lia.
    + simpl in Happ. discriminate Happ.
  - intros H. discriminate H.
Qed.