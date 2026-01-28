Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint string_to_ascii_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_ascii_list s'
  end.

Definition interp_op (op : string) : (Z -> Z -> Z) :=
  if string_dec op "+" then Z.add
  else if string_dec op "-" then Z.sub
  else if string_dec op "*" then Z.mul
  else if string_dec op "//" then Z.div
  else if string_dec op "**" then Z.pow
  else (fun _ _ => 0).

Definition is_in_group1 (op : string) : bool :=
  if string_dec op "+" then true
  else if string_dec op "-" then true
  else false.

Definition is_in_group2 (op : string) : bool :=
  if string_dec op "*" then true
  else if string_dec op "//" then true
  else false.

Definition is_in_group3 (op : string) : bool :=
  if string_dec op "**" then true
  else false.

Fixpoint find_index_aux {A} (p : A -> bool) (l : list A) (n : nat) : option nat :=
  match l with
  | [] => None
  | x :: xs => if p x then Some n else find_index_aux p xs (S n)
  end.

Definition find_index {A} (p : A -> bool) (l : list A) : option nat :=
  find_index_aux p l 0.

Definition rfind_index {A} (p : A -> bool) (l : list A) : option nat :=
  match find_index p (rev l) with
  | Some i => Some ((length l - 1) - i)%nat
  | None => None
  end.

Fixpoint eval_helper (ops : list string) (nums : list Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      match nums with
      | [] => 0
      | [n] => n
      | _::_ =>
          match rfind_index is_in_group1 ops with
          | Some i =>
              let op := nth i ops "" in
              interp_op op
                (eval_helper (firstn i ops) (firstn (S i) nums) fuel')
                (eval_helper (skipn (S i) ops) (skipn (S i) nums) fuel')
          | None =>
              match rfind_index is_in_group2 ops with
              | Some i =>
                  let op := nth i ops "" in
                  interp_op op
                    (eval_helper (firstn i ops) (firstn (S i) nums) fuel')
                    (eval_helper (skipn (S i) ops) (skipn (S i) nums) fuel')
              | None =>
                  match rfind_index is_in_group3 ops with
                  | Some i =>
                      let op := nth i ops "" in
                      interp_op op
                        (eval_helper (firstn i ops) (firstn (S i) nums) fuel')
                        (eval_helper (skipn (S i) ops) (skipn (S i) nums) fuel')
                  | None => 0
                  end
              end
          end
      end
  end.

Definition eval (ops : list string) (nums : list Z) : Z :=
  eval_helper ops nums (length nums).

Definition do_algebra_impl (operators : list string) (operands : list Z) : Z :=
  eval operators operands.

Definition test_operators := ["**"; "*"; "+"].
Definition test_operands := [2; 3; 4; 5]%Z.

Lemma test_case : do_algebra_impl test_operators test_operands = 37.
Proof.
  unfold do_algebra_impl, eval.
  compute.
  reflexivity.
Qed.