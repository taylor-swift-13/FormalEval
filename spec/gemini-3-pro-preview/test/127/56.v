Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope list_scope.
Open Scope string_scope.
Open Scope Z_scope.

Definition simplify (l : list (list Z)) : string :=
  match l with
  | [[n1; d1]; [n2; d2]] =>
      if (n1 * n2) mod (d1 * d2) =? 0 then "YES" else "NO"
  | _ => "NO"
  end.

Example test_case_1: simplify [[7%Z; 13%Z]; [9%Z; 10%Z]] = "NO".
Proof.
  reflexivity.
Qed.