Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint pluck_aux (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => best
  | h :: t =>
      if Z.even h then
        match best with
        | None => pluck_aux t (idx + 1) (Some (h, idx))
        | Some (v, i) =>
            if h <? v then pluck_aux t (idx + 1) (Some (h, idx))
            else pluck_aux t (idx + 1) best
        end
      else pluck_aux t (idx + 1) best
  end.

Definition pluck (l : list Z) : list Z :=
  match pluck_aux l 0 None with
  | None => []
  | Some (v, i) => [v; i]
  end.

Example test_pluck : pluck [0; 1; 2; 5; 3; 7; 9; 10; 7] = [0; 0].
Proof.
  compute. reflexivity.
Qed.