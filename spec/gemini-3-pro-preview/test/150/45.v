Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [-4; -3; -26], output = -26 *)
Example test_x_or_y_neg4 : x_or_y_spec (-4) (-3) (-26) (-26).
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime (-4) -> -26 = -3 *)
    intros Hprime.
    exfalso.
    destruct Hprime as [Hgt _].
    lia.
  - (* Case: ~ prime (-4) -> -26 = -26 *)
    intros _.
    reflexivity.
Qed.