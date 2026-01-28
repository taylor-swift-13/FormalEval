Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else 
    let fix check (i : Z) (fuel : nat) :=
      match fuel with
      | O => true 
      | S f =>
          if i * i >? n then true
          else if (n mod i) =? 0 then false
          else check (i + 1) f
      end
    in check 2 (Z.to_nat n).

Definition intersection (intervals : list (list Z)) : string :=
  match intervals with
  | [a; b] :: [c; d] :: nil =>
      let start := Z.max a c in
      let stop := Z.min b d in
      let len := stop - start in
      if is_prime len then "YES" else "NO"
  | _ => "NO"
  end.

Example test_intersection: intersection [[3%Z; 7%Z]; [3%Z; 7%Z]] = "NO".
Proof.
  compute. reflexivity.
Qed.