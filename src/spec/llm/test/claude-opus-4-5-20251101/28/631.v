Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Fixpoint concatenate (strings : list string) : string :=
  match strings with
  | [] => ""
  | s :: rest => append s (concatenate rest)
  end.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = concatenate strings.

Example test_concatenate_multiple_strings :
  concatenate_spec ["111"; "123"; "456"; "789"; "10"; "11"; "12"; "1"; "14"; "15"; "16"; "17"; "18"; "123"] "11112345678910111211415161718123".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.