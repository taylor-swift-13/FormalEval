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

Example test_case_1 : digits_impl 54 = 5.
Proof.
  unfold digits_impl.
  unfold get_digits.
  simpl.
  (* Compute get_digits 54: since 54 mod 10 = 4, get_digits_helper 54 54 computes 4 :: get_digits_helper 5 53 *)
  (* get_digits_helper 5 53: 5 mod 10 = 5, 5 :: get_digits_helper 0 4 *)
  (* get_digits_helper 0 4: n=0, returns [], so get_digits_helper 5 53 = [5,4] *)
  (* Therefore, get_digits 54 = [4,5] *)
  (* filter odd digits: [4,5] filtered with Nat.odd -> [5] *)
  (* product of [5] = 5 *)
  reflexivity.
Qed.

Example test_case_2 : digits_impl 54 = 5.
Proof.
  unfold digits_impl.
  unfold get_digits.
  simpl.
  reflexivity.
Qed.