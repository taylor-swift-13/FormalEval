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

Definition intersection (l : list (list Z)) : string :=
  match l with
  | [i1; i2] =>
    match i1, i2 with
    | [a; b], [c; d] =>
      let start := Z.max a c in
      let finish := Z.min b d in
      let len := finish - start in
      if is_prime len then "YES" else "NO"
    | _, _ => "NO"
    end
  | _ => "NO"
  end.

Example test_intersection : intersection [[5; 6]; [5; 6]] = "NO".
Proof. reflexivity. Qed.