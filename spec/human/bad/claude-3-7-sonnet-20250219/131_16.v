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

Example test_case_1001 :
  problem_131_spec 1001 1.
Proof.
  unfold problem_131_spec, digits_impl.
  unfold get_digits.
  unfold get_digits_helper.
  simpl.
  (* compute get_digits_helper 1001 1001 step by step: *)
  (* 1001 mod 10 = 1 :: get_digits_helper (1001 / 10 = 100) 1000 *)
  (* 100 mod 10 = 0 :: get_digits_helper (100 / 10 =10) 999 *)
  (* 10 mod 10 = 0 :: get_digits_helper (10 / 10=1) 998 *)
  (* 1 mod 10 = 1 :: get_digits_helper (1 / 10=0) 997 *)
  (* get_digits_helper 0 _ = [] *)
  (* so get_digits 1001 = [1;0;0;1] *)
  (* filter Nat.odd [1;0;0;1] = [1;1] *)
  (* product [1;1] = 1 *)
  reflexivity.
Qed.