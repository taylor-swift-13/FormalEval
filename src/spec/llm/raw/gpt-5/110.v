Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.

Definition exchange_spec (lst1 : list Z) (lst2 : list Z) (res : string) : Prop :=
lst1 <> nil /\ lst2 <> nil /\
(if Nat.leb (length (List.filter (fun x : Z => Z.odd x) lst1))
             (length (List.filter (fun x : Z => Z.even x) lst2))
 then res = "YES" else res = "NO").