Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["How"; "much"; "wood"; "wouisld"; "if"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "woodchuck"] "Howmuchwoodwouisldifwoodchuckchuckifawoodchuckcouldchuckwoodwoodchuck".
Proof.
  unfold problem_28_spec.
  reflexivity.
Qed.