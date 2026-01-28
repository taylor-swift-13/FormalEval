Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.Ascii.
Import ListNotations.
Open Scope Z_scope.

Definition last_digit (n : Z) : Z := Z.abs (n mod 10).

Fixpoint msd_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n mod 10
  | S f => if Z_lt_dec n 10 then n else msd_fuel f (n / 10)
  end.

Definition special_number_b (n : Z) : bool :=
  let abs_n := Z.abs n in
  (10 <? n) && (Z.odd (msd_fuel (Z.to_nat abs_n) abs_n)) && (Z.odd (last_digit abs_n)).

Definition specialFilter_impl (nums : list Z) : Z :=
  Z.of_nat (length (filter special_number_b nums)).

(* 任意整数列表输入均可 *)
Definition problem_146_pre (nums : list Z) : Prop := True.

Definition problem_146_spec (nums : list Z) (output : Z) : Prop :=
  output = specialFilter_impl nums.

Example problem_146_test1 :
  problem_146_spec [5%Z; -2%Z; 1%Z; -5%Z] 0%Z.
Proof.
  unfold problem_146_spec, specialFilter_impl.
  simpl.

  (* We will evaluate special_number_b on each element manually *)

  (* For 5 *)
  assert (H5: special_number_b 5 = false).
  {
    unfold special_number_b.
    (* Evaluate 10 <? 5 *)
    replace (10 <? 5) with false by reflexivity.
    (* false && _ = false *)
    apply Bool.andb_false_l.
  }

  (* For -2 *)
  assert (Hneg2: special_number_b (-2) = false).
  {
    unfold special_number_b.
    (* 10 <? -2 *)
    replace (10 <? -2) with false by reflexivity.
    apply Bool.andb_false_l.
  }

  (* For 1 *)
  assert (H1: special_number_b 1 = false).
  {
    unfold special_number_b.
    replace (10 <? 1) with false by reflexivity.
    apply Bool.andb_false_l.
  }

  (* For -5 *)
  assert (Hneg5: special_number_b (-5) = false).
  {
    unfold special_number_b.
    replace (10 <? -5) with false by reflexivity.
    apply Bool.andb_false_l.
  }

  rewrite H5, Hneg2, H1, Hneg5.
  simpl.
  reflexivity.
Qed.