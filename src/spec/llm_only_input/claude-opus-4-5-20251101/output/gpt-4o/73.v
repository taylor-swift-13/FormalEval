Require Import List.
Require Import Arith.
Require Import Nat.
Require Import ZArith.

Definition smallest_change_spec (arr : list nat) (cnt : nat) : Prop :=
  let arr_reversed := rev arr in
  cnt = fold_left (fun acc i =>
    if nth i arr 0 =? nth i arr_reversed 0 then acc else acc + 1)
    (seq 0 (length arr / 2)) 0.

Definition z_to_nat_list (l : list Z) : list nat :=
  map Z.to_nat l.

Example smallest_change_test : 
  smallest_change_spec (z_to_nat_list (1%Z :: 2%Z :: 3%Z :: 5%Z :: 4%Z :: 7%Z :: 9%Z :: 6%Z :: nil)) 4.
Proof.
  unfold smallest_change_spec.
  unfold z_to_nat_list.
  simpl.
  reflexivity.
Qed.