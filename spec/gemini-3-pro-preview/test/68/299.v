Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (res : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => res
  | x :: xs =>
    if Z.even x then
      match res with
      | None => pluck_aux xs (idx + 1) (Some (x, idx))
      | Some (v, i) =>
        if x <? v then pluck_aux xs (idx + 1) (Some (x, idx))
        else pluck_aux xs (idx + 1) res
      end
    else pluck_aux xs (idx + 1) res
  end.

Definition pluck (l : list Z) : list Z :=
  match pluck_aux l 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_case:
  pluck [10; 9; 8; 7; 6; 7; 6; 5; 4; 3; 2; 1; 7; 4; 7] = [2; 10].
Proof.
  reflexivity.
Qed.