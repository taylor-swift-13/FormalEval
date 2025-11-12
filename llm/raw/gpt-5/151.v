Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.

Open Scope Z_scope.
Open Scope R_scope.

Definition double_the_difference_spec (lst : list R) (ans : Z) : Prop :=
  exists f : list Z,
    length f = length lst /\
    (forall (i : nat) (r : R) (c : Z),
        nth_error lst i = Some r ->
        nth_error f i = Some c ->
        ((exists z : Z, r = IZR z /\ 0 < z /\ Z.odd z = true /\ c = z * z)) \/
        ((~ exists z : Z, r = IZR z /\ 0 < z /\ Z.odd z = true) /\ c = 0)) /\
    ans = fold_right Z.add 0%Z f.