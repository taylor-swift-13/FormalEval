Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix check (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => false
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else check (i + 1) fuel'
      end
    in check 2 (Z.to_nat n).

Definition intersection (intervals : list (list Z)) : string :=
  match intervals with
  | [a; b] :: [c; d] :: nil =>
      let start := Z.max a c in
      let finish := Z.min b d in
      let len := finish - start in
      if is_prime len then "YES" else "NO"
  | _ => "NO"
  end.

Example test_case : intersection [[0%Z; 5%Z]; [6%Z; 10%Z]] = "NO".
Proof.
  compute. reflexivity.
Qed.