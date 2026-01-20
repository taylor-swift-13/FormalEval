Require Import Coq.Strings.Ascii Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition is_uppercase (c : ascii) : bool :=
  let n := nat_of_ascii c in (Nat.leb 65 n) && (Nat.leb n 90).

Fixpoint sum_uppercase_ascii (l : list ascii) : nat :=
  match l with
  | [] => 0
  | c :: t => if is_uppercase c then nat_of_ascii c + sum_uppercase_ascii t
              else sum_uppercase_ascii t
  end.

Definition digitSum_impl (l : list ascii) : nat := sum_uppercase_ascii l.

Example digitSum_impl_abAB: digitSum_impl ("a"%char :: "b"%char :: "A"%char :: "B"%char :: nil) = (131)%nat.
Proof. reflexivity. Qed.

Definition digitSum_spec (l : list ascii) (output : nat) : Prop :=
  output = digitSum_impl l.


