Require Import ZArith.
Require Import List.
Require Import Reals.
Open Scope Z_scope.

Inductive NumValue : Type :=
  | ZVal : Z -> NumValue
  | RVal : R -> NumValue.

Definition is_integer (v : NumValue) : bool :=
  match v with
  | ZVal _ => true
  | RVal _ => false
  end.

Definition get_z_value (v : NumValue) : Z :=
  match v with
  | ZVal z => z
  | RVal _ => 0
  end.

Definition is_positive_odd_integer (v : NumValue) : bool :=
  match v with
  | ZVal n => (n >? 0) && (n mod 2 =? 1)
  | RVal _ => false
  end.

Fixpoint sum_of_squares_of_positive_odd_integers (lst : list NumValue) : Z :=
  match lst with
  | nil => 0
  | x :: xs => if is_positive_odd_integer x 
               then let n := get_z_value x in n * n + sum_of_squares_of_positive_odd_integers xs
               else sum_of_squares_of_positive_odd_integers xs
  end.

Definition double_the_difference_spec (lst : list NumValue) (result : Z) : Prop :=
  result = sum_of_squares_of_positive_odd_integers lst.

Definition test_input : list NumValue :=
  RVal 2.5%R :: RVal 3.7%R :: ZVal 7 :: RVal 10.5%R :: ZVal 24 :: 
  ZVal (-20) :: ZVal (-11) :: RVal (-12.8)%R :: ZVal (-14) :: RVal (-15.3)%R :: 
  ZVal (-16) :: ZVal 19 :: RVal 20.2%R :: RVal 21.9%R :: RVal (-23.8)%R :: 
  ZVal 24 :: ZVal 25 :: ZVal (-9) :: ZVal 26 :: RVal (-27.5)%R :: 
  ZVal (-29) :: ZVal (-28) :: ZVal 24 :: ZVal 19 :: ZVal (-28) :: nil.

Example test_mixed_list : double_the_difference_spec test_input 1396%Z.
Proof.
  unfold double_the_difference_spec.
  unfold test_input.
  simpl.
  reflexivity.
Qed.