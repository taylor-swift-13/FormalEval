Require Import ZArith.
Require Import Reals.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Inductive number : Type :=
| Int : Z -> number
| Real : R -> number.

Definition any_int_spec (x y z : number) (result : bool) : Prop :=
  match x, y, z with
  | Int x', Int y', Int z' =>
      result = true <-> (x' = y' + z' \/ y' = x' + z' \/ z' = y' + x')
  | _, _, _ => result = false
  end.

Example test_any_int : any_int_spec (Real 3.0%R) (Int 4%Z) (Int 7%Z) false.
Proof.
  simpl.
  reflexivity.
Qed.