Require Import String.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition problem_23_pre (input : list string) : Prop := True.

Definition problem_23_spec(input : list string) (output : nat) : Prop :=
  output = fold_left (fun acc s => acc + length s) input 0.

Example test_strlen_mixed :
  problem_23_spec ["one"; "twot"; "three"; "four"; "five"] 24.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.