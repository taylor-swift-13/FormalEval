Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix aux (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => false
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else aux (i + 1) fuel'
      end
    in aux 2 (Z.to_nat n).

Definition intersection (interval_1 interval_2 : list Z) : string :=
  match interval_1, interval_2 with
  | [a; b], [c; d] =>
    let start := Z.max a c in
    let stop := Z.min b d in
    let dist := stop - start in
    if is_prime dist then "YES" else "NO"
  | _, _ => "NO"
  end.

Example test_case_1 : intersection [2%Z; 13%Z] [2%Z; 13%Z] = "YES".
Proof.
  reflexivity.
Qed.