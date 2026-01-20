Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example add_spec_test_case :
  add_spec
    (match nth 0%nat [inl true; inr 7%Z] (inl false) with inl b => if b then 1%Z else 0%Z | inr _ => 0%Z end)
    (match nth 1%nat [inl true; inr 7%Z] (inr 0%Z) with inr z => z | inl _ => 0%Z end)
    8%Z.
Proof.
  unfold add_spec.
  simpl.
  lia.
Qed.