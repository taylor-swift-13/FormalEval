Require Import Coq.Lists.List Coq.Arith.Arith Coq.micromega.Lia.
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

Example test_case_25 :
  problem_131_spec 25 5.
Proof.
  unfold problem_131_spec, digits_impl.
  unfold get_digits.
  unfold get_digits_helper.
  simpl.
  (* get_digits_helper 25 25 unfolds as:  
     25 mod 10 = 5 :: get_digits_helper (25 / 10 = 2) 24
     2 mod 10 = 2 :: get_digits_helper (2 / 10 = 0) 23
     get_digits_helper 0 23 = []
     so get_digits 25 = [5; 2]
  *)
  (* filter Nat.odd [5; 2] = [5] *)
  (* product [5] = 5 *)
  reflexivity.
Qed.