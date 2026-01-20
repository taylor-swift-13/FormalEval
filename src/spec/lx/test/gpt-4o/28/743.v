Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test :
  Spec ["abcdefHello, Woworldrld!"; "a"; "ab"; "abc"; "abcd"; "🦌"; "abcde"; "abcdef"] "abcdefHello, Woworldrld!aababcabcd🦌abcdeabcdef".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.