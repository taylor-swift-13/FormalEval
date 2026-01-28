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
  [VInt 1; VOther; VOther; VOther; VOther; VOther; VOther; VInt 9; VInt 1; VOther] 
  [1; 9; 1].
Proof.
  unfold filter_integers_spec.
  simpl.
  reflexivity.
Qed.