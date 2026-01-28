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

Example test_problem_155 : problem_155_spec (-222222222) (9%nat, 0%nat).
Proof.
  unfold problem_155_spec, even_odd_count_impl.
  (* The fuel calculation involves Z.to_nat on a large number, which causes timeout if evaluated.
     We replace the large fuel with a sufficient small fuel (20) plus the remainder.
     Since the recursion terminates when n reaches 0 (which takes 9 steps),
     any fuel >= 10 yields the same result. *)
  match goal with
  | |- context [to_digits_fuel ?f _] => set (fuel := f)
  end.
  replace fuel with (20 + (fuel - 20))%nat.
  - (* With fuel exposed as (20 + ...), cbn reduces the first 20 steps.
       The computation finishes in 9 steps, and the remaining fuel is discarded. *)
    cbn [to_digits_fuel].
    reflexivity.
  - (* Prove that fuel = 20 + (fuel - 20), which holds if fuel >= 20. *)
    rewrite Nat.add_comm.
    rewrite Nat.add_sub_assoc.
    + rewrite Nat.add_comm. rewrite Nat.add_sub. reflexivity.
    + (* Prove 20 <= fuel *)
      unfold fuel.
      apply le_trans with (m := Z.to_nat 20).
      * simpl. repeat constructor.
      * apply Z2Nat.inj_le; vm_compute; reflexivity.
Qed.