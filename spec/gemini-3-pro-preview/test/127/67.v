Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope list_scope.
Open Scope string_scope.
Open Scope Z_scope.

Definition solution (l : list (list Z)) : string :=
  match l with
  | [a; b] :: [c; d] :: _ =>
    if (Z.max a c <? Z.min b d) then "YES" else "NO"
  | _ => "NO"
  end.

Example test_case: solution [[7%Z; 13%Z]; [3%Z; 10%Z]] = "YES".
Proof.
  reflexivity.
Qed.