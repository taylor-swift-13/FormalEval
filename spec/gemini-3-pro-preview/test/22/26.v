Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope Z_scope.

Inductive val : Type :=
| VInt : Z -> val
| VFloat : R -> val
| VOther : val.

Fixpoint filter_integers_model (l : list val) : list Z :=
  match l with
  | [] => []
  | VInt x :: xs => x :: filter_integers_model xs
  | _ :: xs => filter_integers_model xs
  end.

Definition filter_integers_spec (values : list val) (result : list Z) : Prop :=
  result = filter_integers_model values.

Example test_filter_integers_floats : filter_integers_spec [VFloat 1.5%R; VFloat 2.7%R; VFloat 3.0%R; VFloat (-51.08332919278058)%R; VFloat (-4.6)%R] [].
Proof.
  unfold filter_integers_spec.
  simpl.
  reflexivity.
Qed.