Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test :
  Spec ["The"; "quick"; "woood"; "brown"; "Hellsingleo, World!"; "jumps"; "fox"; "11"; "extra"; "the"; "lazy"; "over"]
       "ThequickwooodbrownHellsingleo, World!jumpsfox11extrathelazyover".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.