Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

(* Auxiliary function 1.1: sum of decimal digits with fuel *)
Fixpoint sum_decimal_digits_aux (fuel n : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f' =>
    match n with
    | 0 => 0
    | _ => (n mod 10) + sum_decimal_digits_aux f' (n / 10)
    end
  end.

(* Main function 1: sum of decimal digits *)
Definition sum_decimal_digits (n : nat) : nat :=
  sum_decimal_digits_aux n n.

(* Auxiliary function 2.1: converting positive nat to binary string with fuel *)
Fixpoint nat_to_binary_string_pos_aux (fuel n : nat) : string :=
  match fuel with
  | 0 => ""
  | S f' =>
    if Nat.eqb n 0 then ""
    else nat_to_binary_string_pos_aux f' (n / 2) ++ (if Nat.eqb (n mod 2) 0 then "0" else "1")
  end.

(* Main function 2: convert nat to binary string *)
Definition nat_to_binary_string (n : nat) : string :=
  if Nat.eqb n 0 then "0"
  else nat_to_binary_string_pos_aux n n.

(* Complete solve implementation *)
Definition solve_impl (N : nat) : string :=
  nat_to_binary_string (sum_decimal_digits N).

Definition problem_84_pre (N : nat) : Prop := (N <= 10000)%nat.

Definition problem_84_spec (N : nat) (output : string) : Prop :=
  output = solve_impl N.

(* Instead of defining a general sum_digits function using a fixpoint with an argument that is not structurally smaller,
   we use the existing sum_decimal_digits_aux correctness by reasoning with fuel *)

(* Lemma: sum_decimal_digits_aux correctly sums digits when fuel is large enough *)
Lemma sum_decimal_digits_aux_correct : forall n fuel,
    fuel >= n ->
    sum_decimal_digits_aux fuel n =
    (if n =? 0 then 0 else (n mod 10) + sum_decimal_digits_aux fuel (n / 10)).
Proof.
  intros n fuel Hfuel.
  destruct fuel as [|f'].
  - lia.
  - destruct n; simpl.
    + reflexivity.
    + reflexivity.
Qed.

(* Lemma: sum_decimal_digits computes the correct sum *)
Lemma sum_decimal_digits_correct : forall n,
    sum_decimal_digits n =
    (if n =? 0 then 0 else (n mod 10) + sum_decimal_digits_aux n (n / 10)).
Proof.
  intros n.
  unfold sum_decimal_digits.
  rewrite sum_decimal_digits_aux_correct.
  - reflexivity.
  - lia.
Qed.

(* We will calculate sum_decimal_digits 1000 step-by-step *)
Lemma sum_decimal_digits_1000 : sum_decimal_digits 1000 = 1.
Proof.
  unfold sum_decimal_digits.
  (* fuel = 1000 *)
  revert 1000.
  induction 1000 using lt_wf_ind.
  intros fuel Hfuel.
  simpl.
  (* n = 1000 *)
  rewrite Nat.eqb_neq; [|lia].
  simpl.
  rewrite (sum_decimal_digits_aux_correct (fuel:=fuel) (n:=1000)); [|lia].
  (* now sum_decimal_digits_aux fuel (1000/10) *)
  assert (1000 / 10 = 100) by reflexivity.
  rewrite H.
  (* Recursively evaluate sum_decimal_digits_aux fuel 100 *)
  clear H.
  remember (sum_decimal_digits_aux fuel 100) as R.
  (* Use IH if fuel >= 100 *)
  assert (fuel >= 100) by lia.
  rewrite (sum_decimal_digits_aux_correct (fuel:=fuel) (n:=100)) in HeqR by assumption.
  rewrite Nat.eqb_neq in HeqR; [|lia].
  simpl in HeqR.
  rewrite (sum_decimal_digits_aux_correct (fuel:=fuel) (n:=100/10)) in HeqR by lia.
  rewrite Nat.eqb_neq; [|lia].
  
  (* 100 / 10 = 10 *)
  assert (100 / 10 = 10) by reflexivity.
  rewrite H0 in HeqR.
  simpl in HeqR.

  (* Similarly unwrap down to 1 *)
  remember (sum_decimal_digits_aux fuel 10) as R10.
  rewrite (sum_decimal_digits_aux_correct (fuel:=fuel) (n:=10)) in HeqR10 by lia.
  rewrite Nat.eqb_neq in HeqR10; [|lia].
  simpl in HeqR10.

  (* 10 / 10 = 1 *)
  assert (10 / 10 = 1) by reflexivity.
  rewrite H1 in HeqR10.
  simpl in HeqR10.

  remember (sum_decimal_digits_aux fuel 1) as R1.
  rewrite (sum_decimal_digits_aux_correct (fuel:=fuel) (n:=1)) in HeqR1 by lia.
  rewrite Nat.eqb_neq in HeqR1; [|lia].
  simpl in HeqR1.

  (* 1 / 10 = 0 *)
  assert (1 / 10 = 0) by reflexivity.
  rewrite H2 in HeqR1.
  simpl in HeqR1.
  (* sum_decimal_digits_aux fuel 0 = 0 *)
  rewrite (sum_decimal_digits_aux_correct (fuel:=fuel) (n:=0)) in HeqR1 by lia.
  simpl in HeqR1.

  (* Evaluate now R1 *)
  simpl in HeqR1.
  rewrite Nat.eqb_refl in HeqR1.
  simpl in HeqR1.
  rewrite HeqR1.

  (* sum_decimal_digits_aux fuel 1 = 1 + 0 = 1 *)
  rewrite HeqR1 in HeqR10.
  simpl in HeqR10.
  rewrite HeqR1 in HeqR10.

  (* sum_decimal_digits_aux fuel 10 = 0 + 1 = 1 *)
  rewrite HeqR10 in HeqR.
  simpl in HeqR.
  rewrite HeqR10 in HeqR.

  (* sum_decimal_digits_aux fuel 100 = 0 + 1 = 1 *)
  rewrite HeqR in *.
  simpl.

  (* Finally sum_decimal_digits_aux fuel 1000 = 0 + 1 = 1 *)
  lia.
Qed.

(* Prove nat_to_binary_string on 1 yields "1" *)
Lemma nat_to_binary_string_1 : nat_to_binary_string 1 = "1".
Proof.
  unfold nat_to_binary_string.
  (* 1 =? 0 = false *)
  rewrite Nat.eqb_neq; [|lia].
  (* nat_to_binary_string_pos_aux 1 1 *)
  simpl.
  (* fuel = 1 *)
  (* n = 1, n/2 = 0 *)
  rewrite Nat.eqb_neq; [|lia].
  simpl.
  (* recursive call fuel=0 n=0 returns "" *)
  simpl.
  rewrite Nat.eqb_refl.
  simpl.
  (* bit: (1 mod 2) = 1 so "1" *)
  reflexivity.
Qed.

(* Final test case proof *)
Example test_case_1000 :
  problem_84_spec 1000 "1".
Proof.
  unfold problem_84_spec, solve_impl.
  rewrite sum_decimal_digits_1000.
  apply nat_to_binary_string_1.
Qed.