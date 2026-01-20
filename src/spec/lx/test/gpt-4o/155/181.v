(* Required imports *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Definition of count_digits_acc *)
Fixpoint count_digits_acc (l : list Z) (acc : Z * Z) : Z * Z :=
  match l with
  | nil => acc
  | h :: t =>
    let '(even_count, odd_count) := acc in
    if Z.even h then
      count_digits_acc t (even_count + 1, odd_count)
    else
      count_digits_acc t (even_count, odd_count + 1)
  end.

(* Definition of to_digits_fuel *)
Fixpoint to_digits_fuel (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => nil
  | S f' =>
    if n =? 0 then
      nil
    else
      (Z.abs (n mod 10)) :: to_digits_fuel f' (n / 10)
  end.

(* Specification of even_odd_count *)
Definition even_odd_count_spec (num : Z) (output : Z * Z) : Prop :=
  let digits := to_digits_fuel (Z.to_nat (Z.abs num) + 1) num in
  let '(even_c, odd_c) := count_digits_acc digits (0, 0) in
  output = (even_c, odd_c).

(* Test case *)
Example even_odd_count_test :
  even_odd_count_spec 20%Z (2, 0).
Proof.
  unfold even_odd_count_spec.
  simpl.
  (* Convert 20 to digits *)
  simpl. reflexivity.
Qed.