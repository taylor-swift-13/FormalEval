
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition digits (x : Z) : nat :=
  let s := Z.to_string x in
  let len := String.length s in
  match String.get 0 s with
  | Some "-" => len - 1
  | _ => len
  end.

Definition add_elements_spec (arr : list Z) (k : nat) (sum : Z) : Prop :=
  1 <= length arr <= 100 /\
  1 <= k <= length arr /\
  sum = 
    fold_left Z.add
      (filter (fun x => Nat.leb (digits x) 2) (firstn k arr))
      0.
