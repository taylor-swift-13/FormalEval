
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

Fixpoint digits_of_nat (n : nat) : list Z :=
  match n with
  | O => [0]
  | S _ => let fix aux (m : nat) (acc : list Z) :=
             match m with
             | O => match acc with [] => [0] | _ => acc end
             | S _ => aux (Nat.div m 10) ((Z.of_nat (Nat.modulo m 10)) :: acc)
             end
           in aux n []
  end.

Definition sum_of_digits (n : Z) : Z :=
  let digits := digits_of_nat (Z.to_nat n) in
  fold_left Z.add digits 0.

Fixpoint nat_to_binary_string (n : nat) : string :=
  match n with
  | O => "0"
  | S O => "1"
  | _ => let q := Nat.div n 2 in
         let r := Nat.modulo n 2 in
         append (nat_to_binary_string q)
                (if Nat.eqb r 0 then "0" else "1")
  end.

Definition Z_to_binary_string (z : Z) : string :=
  match z with
  | Z0 => "0"
  | Zpos p => nat_to_binary_string (Pos.to_nat p)
  | Zneg _ => "0"
  end.

Definition solve_spec (N : Z) (result : string) : Prop :=
  0 <= N <= 10000 /\
  result = Z_to_binary_string (sum_of_digits N).
