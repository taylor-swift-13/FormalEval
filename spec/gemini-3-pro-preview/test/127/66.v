Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition simplify (l : list (list Z)) : string :=
  match l with
  | [x; n] =>
    match x, n with
    | [num_x; den_x], [num_n; den_n] =>
      if (num_x * num_n) mod (den_x * den_n) =? 0 then "YES" else "NO"
    | _, _ => "NO"
    end
  | _ => "NO"
  end.

Example check_simplify_new : simplify [[-15; 12]; [-15; 12]] = "NO".
Proof. reflexivity. Qed.