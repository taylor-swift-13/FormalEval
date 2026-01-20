
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Import ListNotations.

Open Scope Z_scope.

Fixpoint tri_value (n : Z) : Q :=
  match n with
  | 0 => 1
  | 1 => 3
  | _ => if Z.even n then 1 + (inject_Z n) / 2
         else tri_value (n - 1) + tri_value (n - 2) + 1 + (inject_Z (n + 1)) / 2
  end.

Fixpoint tri_list_aux (n : nat) (current : Z) : list Q :=
  match n with
  | O => []
  | S n' => tri_value current :: tri_list_aux n' (current + 1)
  end.

Definition tri_list (n : Z) : list Q :=
  if n <? 0 then []
  else tri_list_aux (Z.to_nat (n + 1)) 0.

Definition tri_spec (n : Z) (result : list Q) : Prop :=
  n >= 0 ->
  length result = Z.to_nat (n + 1) /\
  (forall i : nat, (Z.of_nat i <= n)%Z ->
    nth i result 0 = tri_value (Z.of_nat i)).
