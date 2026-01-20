Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_complex :
  Spec ["python"; "is"; "pythonhello"; "a"; "pyothonhello"; "pythgreat789on"; "great"; "language"; "is"; "language"] "pythonispythonhelloapyothonhellopythgreat789ongreatlanguageislanguage".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.