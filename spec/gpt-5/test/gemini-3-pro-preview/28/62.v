Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["orana45e6ge"; "apple"; "banaworldaana"; "banana"; "orange"] "orana45e6geapplebanaworldaanabananaorange".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.