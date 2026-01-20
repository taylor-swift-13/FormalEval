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
  concatenate_spec ["a"; "ab"; "abcd"; "🦌"; "abcde"; "achara1longctersbc8789d"; "abcdef"] "aababcd🦌abcdeachara1longctersbc8789dabcdef".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.