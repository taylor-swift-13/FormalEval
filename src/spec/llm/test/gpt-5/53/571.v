Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Definition to_Z_of_input (e : bool + Z) : Z :=
  match e with
  | inl b => if b then 1%Z else 0%Z
  | inr z => z
  end.

Example add_spec_test_case :
  add_spec
    (to_Z_of_input (nth 0%nat [inl true; inr (-999998%Z)] (inr 0%Z)))
    (to_Z_of_input (nth 1%nat [inl true; inr (-999998%Z)] (inr 0%Z)))
    (-999997%Z).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.