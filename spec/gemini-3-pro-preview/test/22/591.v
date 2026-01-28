Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Inductive val : Type :=
| VInt : Z -> val
| VOther : val.

Fixpoint filter_integers_model (l : list val) : list Z :=
  match l with
  | [] => []
  | VInt x :: xs => x :: filter_integers_model xs
  | VOther :: xs => filter_integers_model xs
  end.

Definition filter_integers_spec (values : list val) (result : list Z) : Prop :=
  result = filter_integers_model values.

Example test_filter_integers_1 : filter_integers_spec 
  [VOther; VOther; VInt (-6); VOther; VOther; VOther; VInt 5; VOther; VInt (-7); VInt 0; VOther; VInt 51; VOther; VOther; VOther; VOther; VOther; VOther; VOther; VOther; VInt 5; VInt (-7)] 
  [-6; 5; -7; 0; 51; 5; -7].
Proof.
  unfold filter_integers_spec.
  simpl.
  reflexivity.
Qed.