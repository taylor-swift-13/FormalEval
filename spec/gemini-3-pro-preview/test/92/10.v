Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Reals.Reals.
Open Scope Z_scope.

Inductive any_int_arg : Type :=
| ArgZ (z : Z)
| ArgR (r : R).

Definition any_int_spec (x y z : any_int_arg) (res : bool) : Prop :=
  match x, y, z with
  | ArgZ x, ArgZ y, ArgZ z => res = true <-> (x = y + z \/ y = x + z \/ z = x + y)
  | _, _, _ => res = false
  end.

Example test_any_int : any_int_spec (ArgR 3.0%R) (ArgZ 4%Z) (ArgZ 7%Z) false.
Proof.
  simpl.
  reflexivity.
Qed.