Require Import Coq.Lists.List Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_digits_helper (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | 0%nat => []
  | S f' =>
    match n with
    | 0 => []
    | _ => (n mod 10) :: get_digits_helper (n / 10) f'
    end
  end.

Definition get_digits (n : Z) : list Z :=
  get_digits_helper n 500%nat.

Fixpoint product (l : list Z) : Z :=
  match l with
  | [] => 1
  | h :: t => h * product t
  end.

Definition digits_impl (n : Z) : Z :=
  let ds := filter Z.odd (get_digits n) in
  match ds with
  | [] => 0
  | _ => product ds
  end.

Definition problem_131_pre (n : Z) : Prop := n > 0.

Definition problem_131_spec (n : Z) (output : Z) : Prop :=
  output = digits_impl n.

Example test_case : problem_131_spec 124834738571930288374895092375830274843252127479238048384758941827309258429539458173975894729347587 331372541566669015602447805107421875.
Proof.
  unfold problem_131_spec.
  unfold digits_impl.
  unfold get_digits.
  vm_compute.
  reflexivity.
Qed.