Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_python :
  Spec ["python"; "is"; "pythonhello"; "a"; "great"; "language"; "is"; "is"] "pythonispythonhelloagreatlanguageisis".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.