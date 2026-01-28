Require Import Coq.Lists.List Coq.Arith.Arith Coq.ZArith.ZArith Coq.Micromega.Lia.
Import ListNotations.

Fixpoint get_digits_helper (n fuel : nat) : list nat :=
  match fuel with
  | 0 => []
  | S f' =>
    match n with
    | 0 => []
    | _ => (n mod 10) :: get_digits_helper (n / 10) f'
    end
  end.

Definition get_digits (n : nat) : list nat :=
  get_digits_helper n n.

Fixpoint product (l : list nat) : nat :=
  match l with
  | [] => 1
  | h :: t => h * product t
  end.

Definition digits_impl (n : nat) : nat :=
  let ds := filter Nat.odd (get_digits n) in
  match ds with
  | [] => 0
  | _ => product ds
  end.

(* n 为正整数 *)
Definition problem_131_pre (n : nat) : Prop := n > 0.

Definition problem_131_spec (n : nat) (output : nat) : Prop :=
  output = digits_impl n.

Lemma helper_step : forall n f, f <> 0 -> 
  get_digits_helper n f = match n with 0 => [] | _ => (n mod 10) :: get_digits_helper (n/10) (pred f) end.
Proof.
  intros. destruct f. contradiction. simpl. reflexivity.
Qed.

Lemma helper_zero : forall f, get_digits_helper 0 f = [].
Proof.
  destruct f; simpl; auto.
Qed.

Ltac reduce_digit :=
  match goal with
  | [ |- context [ get_digits_helper (Z.to_nat ?n) ?f ] ] =>
    rewrite helper_step; [
      rewrite Z2Nat.inj_mod by lia;
      rewrite Z2Nat.inj_div by lia;
      change (Z.of_nat 10) with 10%Z;
      let d_term := constr:((n mod 10)%Z) in
      let d := eval compute in d_term in
      let n_term := constr:((n / 10)%Z) in
      let n' := eval compute in n_term in
      replace (n mod 10)%Z with d by reflexivity;
      replace (n / 10)%Z with n' by reflexivity;
      simpl Z.to_nat at 1
    | 
      apply Nat.neq_0_lt_0; apply Z2Nat.inj_lt; lia
    ]
  end.

Example test_case : problem_131_spec (Z.to_nat 135797536) 99225.
Proof.
  unfold problem_131_spec, digits_impl.
  replace (get_digits (Z.to_nat 135797536)) with [6; 3; 5; 7; 9; 7; 5; 3; 1].
  - simpl. reflexivity.
  - unfold get_digits.
    repeat reduce_digit.
    rewrite helper_zero.
    reflexivity.
Qed.