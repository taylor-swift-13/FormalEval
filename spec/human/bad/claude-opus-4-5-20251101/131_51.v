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

Definition digits_of_135797534 : list nat := [4; 3; 5; 7; 9; 7; 5; 3; 1].

Definition odd_digits_of_135797534 : list nat := [3; 5; 7; 9; 7; 5; 3; 1].

Lemma get_digits_135797534 : get_digits 135797534 = digits_of_135797534.
Proof.
  native_compute.
  reflexivity.
Qed.

Lemma filter_odd_digits : filter Nat.odd digits_of_135797534 = odd_digits_of_135797534.
Proof.
  native_compute.
  reflexivity.
Qed.

Lemma product_odd_digits : product odd_digits_of_135797534 = 99225.
Proof.
  native_compute.
  reflexivity.
Qed.

Example test_digits_135797534 : problem_131_spec 135797534 99225.
Proof.
  unfold problem_131_spec.
  unfold digits_impl.
  rewrite get_digits_135797534.
  rewrite filter_odd_digits.
  rewrite product_odd_digits.
  reflexivity.
Qed.