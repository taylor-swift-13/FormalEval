Require Import ZArith.
Require Import List.
Require Import Reals.
Require Import Lra.
Require Import Lia.
Open Scope Z_scope.

Definition is_positive_odd_integer (n : Z) : bool :=
  (n >? 0) && (n mod 2 =? 1).

Fixpoint sum_of_squares_of_positive_odd_integers (lst : list R) : Z :=
  match lst with
  | nil => 0
  | x :: xs => 
      let z := Z_of_R x in
      if Req_dec x (IZR z) then
         if is_positive_odd_integer z 
         then z * z + sum_of_squares_of_positive_odd_integers xs
         else sum_of_squares_of_positive_odd_integers xs
      else sum_of_squares_of_positive_odd_integers xs
  end.

Definition double_the_difference_spec (lst : list R) (result : Z) : Prop :=
  result = sum_of_squares_of_positive_odd_integers lst.

Example test_case_1 : double_the_difference_spec (1.0%R :: 3.5%R :: -4.6%R :: nil) 1%Z.
Proof.
  unfold double_the_difference_spec.
  simpl.
  replace (Z_of_R 1.0%R) with 1%Z by apply Z_of_R_IZR.
  destruct (Req_dec 1 (IZR 1)) as [_|Hneq].
  2: { exfalso; apply Hneq; reflexivity. }
  simpl.
  destruct (Req_dec 3.5 (IZR (Z_of_R 3.5))) as [Heq|Hneq].
  { 
    exfalso.
    apply (f_equal (fun x => x * 2)%R) in Heq.
    replace (3.5 * 2)%R with 7%R in Heq by lra.
    rewrite <- mult_IZR in Heq.
    apply eq_IZR_eq in Heq.
    lia.
  }
  destruct (Req_dec (-4.6) (IZR (Z_of_R (-4.6)))) as [Heq|Hneq].
  {
    exfalso.
    apply (f_equal (fun x => x * 10)%R) in Heq.
    replace (-4.6 * 10)%R with (-46)%R in Heq by lra.
    rewrite <- mult_IZR in Heq.
    apply eq_IZR_eq in Heq.
    lia.
  }
  reflexivity.
Qed.