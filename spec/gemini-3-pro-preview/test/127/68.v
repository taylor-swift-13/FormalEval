Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix aux (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => true
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else aux (i + 1) fuel'
      end
    in aux 2 (Z.to_nat n).

Definition intersection (l1 l2 : list Z) : string :=
  match l1, l2 with
  | [a; b], [c; d] =>
      let start := Z.max a c in
      let finish := Z.min b d in
      let len := Z.max 0 (finish - start) in
      if is_prime len then "YES" else "NO"
  | _, _ => "NO"
  end.

Example test_case_1 : intersection [1%Z; 5%Z] [-1%Z; 7%Z] = "NO".
Proof. reflexivity. Qed.