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

Definition digits_of_135797531 : list nat := [1; 3; 5; 7; 9; 7; 5; 3; 1].

Definition odd_digits_of_135797531 : list nat := [1; 3; 5; 7; 9; 7; 5; 3; 1].

Lemma product_odd_digits_135797531 : product odd_digits_of_135797531 = 99225.
Proof.
  unfold odd_digits_of_135797531.
  simpl.
  reflexivity.
Qed.

Lemma filter_odd_all_odd : filter Nat.odd [1; 3; 5; 7; 9; 7; 5; 3; 1] = [1; 3; 5; 7; 9; 7; 5; 3; 1].
Proof.
  simpl.
  reflexivity.
Qed.

Lemma get_digits_helper_135797531 : 
  get_digits_helper 135797531 10 = [1; 3; 5; 7; 9; 7; 5; 3; 1].
Proof.
  native_compute.
  reflexivity.
Qed.

Lemma digits_impl_135797531 : digits_impl 135797531 = 99225.
Proof.
  unfold digits_impl.
  unfold get_digits.
  rewrite <- (get_digits_helper_135797531).
  assert (H: get_digits_helper 135797531 135797531 = get_digits_helper 135797531 10).
  { native_compute. reflexivity. }
  rewrite H.
  rewrite get_digits_helper_135797531.
  rewrite filter_odd_all_odd.
  simpl.
  reflexivity.
Qed.

Example test_digits_135797531 : problem_131_spec 135797531 99225.
Proof.
  unfold problem_131_spec.
  exact digits_impl_135797531.
Qed.