Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_large_concat :
  problem_28_spec ["12"; "456"; "789"; "10"; "11"; "12"; "13"; "14"; "lazyy"; "15"; "16"; "thea"; "lazy"; "3113"; "18"; "11"; "3113"; "10"; "12"]
                  "124567891011121314lazyy1516thealazy3113181131131012".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.