Require Import Coq.Lists.List Coq.Strings.Ascii Coq.ZArith.ZArith Coq.Arith.Arith.
Open Scope Z_scope.

Fixpoint count_digits_acc (l : list Z) (acc : nat * nat) : nat * nat :=
  match l with
  | nil => acc
  | h :: t =>
      let '(e,o) := acc in
      if Z.even h
      then count_digits_acc t (S e, o)
      else count_digits_acc t (e, S o)
  end.

Fixpoint to_digits_fuel (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => nil
  | S f' =>
      let p := Z.abs n in
      if p =? 0 then nil else (p mod 10) :: to_digits_fuel f' (p / 10)
  end.

Definition even_odd_count_impl (num : Z) : nat * nat :=
  count_digits_acc (to_digits_fuel (Z.to_nat (Z.abs num) + 1)%nat num) (0%nat, 0%nat).

(* 任意整数输入 *)
Definition problem_155_pre (num : Z) : Prop := True.

Definition problem_155_spec (num : Z) (output : nat * nat) : Prop :=
  output = even_odd_count_impl num.

Example test_problem_155 : problem_155_spec (-6) (1%nat, 0%nat).
Proof.
  (* Unfold the specification definition *)
  unfold problem_155_spec.
  (* Unfold the implementation definition to expose the underlying function calls *)
  unfold even_odd_count_impl.
  (* 
     Since the input is a concrete integer constant (-6) and the logic involves 
     computable functions (Fixpoints on Z and nat), we can use vm_compute 
     to evaluate the right-hand side completely.
  *)
  vm_compute.
  (* The evaluation results in (1, 0), which matches the left-hand side. *)
  reflexivity.
Qed.