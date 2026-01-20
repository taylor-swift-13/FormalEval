
Require Import Reals.
Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope R_scope.

Definition ceiling (x : R) : Z :=
  Zceil x.

Definition square_Z (z : Z) : Z :=
  (z * z)%Z.

Fixpoint sum_Z (lst : list Z) : Z :=
  match lst with
  | [] => 0%Z
  | h :: t => (h + sum_Z t)%Z
  end.

Definition sum_squares_spec (lst : list R) (result : Z) : Prop :=
  result = sum_Z (map (fun x => square_Z (ceiling x)) lst).
