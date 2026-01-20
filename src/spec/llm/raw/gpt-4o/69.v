
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical_Prop.

Definition search_spec (lst : list nat) (result : nat) : Prop :=
  let count := fold_left (fun acc x =>
                            if Nat.eqb (count_occ Nat.eq_dec lst x) 0 then acc
                            else (x, count_occ Nat.eq_dec lst x) :: acc) lst [] in
  (result = -1 /\ (forall num cnt, In (num, cnt) count -> cnt < num)) \/
  (exists num cnt, In (num, cnt) count /\ cnt >= num /\ result = max num result).
