
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Definition digits (x : Z) : nat :=
  let s := Z.to_string x in
  if (String.get 0 s =? "-")%string then
    String.length s - 1
  else
    String.length s.

Definition add_elements_spec (arr : list Z) (k : nat) (sum : Z) : Prop :=
  1 <= length arr <= 100 /\
  1 <= k <= length arr /\
  sum = fold_right Z.add 0 (filter (fun x => Nat.leb (digits x) 2) (firstn k arr)).
