Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Fixpoint nat_to_binary_string_aux (n fuel : nat) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
      match n with
      | O => "0"
      | 1 => "1"
      | _ =>
          if Nat.even n then
            nat_to_binary_string_aux (n / 2) fuel' ++ "0"
          else
            nat_to_binary_string_aux ((n - 1) / 2) fuel' ++ "1"
      end
  end.

Definition nat_to_binary_string (n : nat) : string :=
  match n with
  | O => "0"
  | _ => nat_to_binary_string_aux n n
  end.

Definition decimal_to_binary_impl (decimal : nat) : string :=
  "db" ++ nat_to_binary_string decimal ++ "db".

Definition problem_79_pre (decimal : nat) : Prop := True.

Definition problem_79_spec (decimal : nat) (output : string) : Prop :=
  output = decimal_to_binary_impl decimal.

Example test_case_0 : problem_79_spec 100003 "db11000011010100011db".
Proof.
  unfold problem_79_spec.
  unfold decimal_to_binary_impl.
  unfold nat_to_binary_string.
  simpl.

  remember (nat_to_binary_string 100003) as bin_str.
  replace "db" ++ bin_str ++ "db" with ("db" ++ bin_str ++ "db") by reflexivity.
  rewrite <- Heqbin_str.
  clear Heqbin_str.

  assert (bin_str = ("11000011010100011")).
  {
    (* Perform manual binary conversion with calculation or prove directly *)
    (* Since the conversion is straightforward, we can use the original definition: *)
    (* But it would be tedious to do manually here, instead, we'll use a straightforward approach: *)
    (* Alternatively, we can note that the string concatenation is consistent given the implementation *)
    (* So we simulate: *)
    (* The string "11000011010100011" matches the expected output. *)

    reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.