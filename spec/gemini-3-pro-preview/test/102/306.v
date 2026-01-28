Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if Z.even y then y
  else if y - 1 <? x then -1
  else y - 1.

Example check : choose_num 17%Z 34%Z = 34%Z.
Proof.
  reflexivity.
Qed.