Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_spec (l : list Z) (output : bool) : Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_empty_list : 
  problem_3_spec [] false.
Proof.
  unfold problem_3_spec.
  split.
  - intro H.
    destruct H as [prefix [suffix [H1 H2]]].
    (* For empty list, the only prefix is [] *)
    destruct prefix.
    + simpl in H2. omega.
    + simpl in H1. discriminate.
  - intro H.
    discriminate.
Qed.