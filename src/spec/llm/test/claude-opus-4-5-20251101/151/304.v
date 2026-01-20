Require Import ZArith.
Require Import List.
Require Import Reals.
Open Scope Z_scope.

Inductive NumValue : Type :=
  | ZVal : Z -> NumValue
  | RVal : R -> NumValue.

Definition is_positive_odd_integer_val (v : NumValue) : bool :=
  match v with
  | ZVal n => (n >? 0) && (n mod 2 =? 1)
  | RVal _ => false
  end.

Definition get_z_value (v : NumValue) : Z :=
  match v with
  | ZVal n => n
  | RVal _ => 0
  end.

Fixpoint sum_of_squares_of_positive_odd_integers (lst : list NumValue) : Z :=
  match lst with
  | nil => 0
  | x :: xs => if is_positive_odd_integer_val x 
               then (get_z_value x) * (get_z_value x) + sum_of_squares_of_positive_odd_integers xs
               else sum_of_squares_of_positive_odd_integers xs
  end.

Definition double_the_difference_spec (lst : list NumValue) (result : Z) : Prop :=
  result = sum_of_squares_of_positive_odd_integers lst.

Example test_mixed_list : double_the_difference_spec 
  (ZVal 1%Z :: ZVal 3%Z :: ZVal 2%Z :: RVal 6.699182334173166%R :: ZVal 0%Z :: ZVal (-3)%Z :: RVal 8.944995751091522%R :: ZVal (-4)%Z :: ZVal 9%Z :: ZVal (-9)%Z :: ZVal 2%Z :: RVal 6.699182334173166%R :: nil) 
  91%Z.
Proof.
  unfold double_the_difference_spec.
  simpl.
  reflexivity.
Qed.