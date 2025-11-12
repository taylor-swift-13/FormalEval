
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition even (x : Z) : Prop := Z.even x = true.
Definition odd (x : Z) : Prop := Z.odd x = true.

Definition all_even (l : list Z) : Prop := Forall even l.

Definition count (P : Z -> Prop) (l : list Z) : nat :=
  length (filter (fun x => if (Z.eqb (Z.b2z (P x)) 1) then true else false) l).

Definition exchange_spec (lst1 lst2 : list Z) (res : string) : Prop :=
  let cnt_odd := length (filter (fun x => Z.odd x = true) lst1) in
  let cnt_even := length (filter (fun x => Z.even x = true) lst2) in
  res = if Nat.leb cnt_odd cnt_even then "YES" else "NO".
