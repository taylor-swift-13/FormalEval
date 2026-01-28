Require Import Coq.Lists.List Coq.Arith.Arith.
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

Definition problem_131_pre (n : nat) : Prop := n > 0.

Definition problem_131_spec (n : nat) (output : nat) : Prop :=
  output = digits_impl n.

Lemma get_digits_995 : get_digits 995 = [5; 9; 9].
Proof.
  unfold get_digits.
  unfold get_digits_helper.
  reflexivity.
Qed.

Lemma filter_odd_5_9_9 : filter Nat.odd [5; 9; 9] = [5; 9; 9].
Proof.
  reflexivity.
Qed.

Lemma product_5_9_9 : product [5; 9; 9] = 405.
Proof.
  reflexivity.
Qed.

Example test_digits_995 : problem_131_spec 995 405.
Proof.
  unfold problem_131_spec.
  unfold digits_impl.
  rewrite get_digits_995.
  rewrite filter_odd_5_9_9.
  rewrite product_5_9_9.
  reflexivity.
Qed.