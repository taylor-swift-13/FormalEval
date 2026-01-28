Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition intersection (l : list (list Z)) : string :=
  match l with
  | [a::b::[]; c::d::[]] =>
      let start := Z.max a c in
      let end_ := Z.min b d in
      if start <=? end_ then "NO" else "YES"
  | _ => "NO"
  end.

Example test_case: intersection [[-10%Z; 10%Z]; [-10%Z; 10%Z]] = "NO".
Proof. reflexivity. Qed.