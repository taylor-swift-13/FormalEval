(* 导入 Coq 的标准库 *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(*
  辅助函数 check_parens_inner
*)
Fixpoint check_parens_inner (l : list ascii) (counter : nat) : bool :=
  match l with
  | [] => Nat.eqb counter 0
  | "(" % char :: t => check_parens_inner t (S counter)
  | ")" % char :: t =>
    match counter with
    | 0 => false
    | S n' => check_parens_inner t n'
    end
  | _ :: t => check_parens_inner t counter
  end.

(*
  is_balanced 函数
  修正：现在直接接收一个 list ascii 作为输入。
*)
Definition is_balanced (l : list ascii) : bool :=
  check_parens_inner l 0.

Definition match_parens_impl (inputs : list (list ascii)) : string :=
  match inputs with
  | [s1; s2] =>
    (* "++" 现在是列表拼接操作符 *)
    if orb (is_balanced (s1 ++ s2)) (is_balanced (s2 ++ s1))
    then "Yes"%string
    else "No"%string
  | _ => "No"%string (* 处理非预期输入，例如列表长度不为2 *)
  end.

Definition match_parens (inputs : list string) : string :=
  match_parens_impl (map list_ascii_of_string inputs).

(* 输入列表长度为 2，且每个字符仅为 '(' 或 ')' *)
Definition problem_119_pre (inputs : list string) : Prop :=
  length inputs = 2 /\ Forall (fun s =>
    let l := list_ascii_of_string s in
    Forall (fun c => c = "("%char \/ c = ")"%char) l) inputs.

Definition problem_119_spec (inputs : list string) (output : string) : Prop :=
  output = match_parens inputs.

(* Test case verification *)
Example test_match_parens : problem_119_spec ["()((("%string; "((((())))))))))(())"%string] "No"%string.
Proof.
  (* Unfold the specification definition *)
  unfold problem_119_spec.
  
  (* Unfold the main function definition *)
  unfold match_parens.
  
  (* Since the input is concrete, we can evaluate the function directly.
     vm_compute is efficient for string and list manipulations. *)
  vm_compute.
  
  (* The evaluation results in "No" = "No", which is reflexively true. *)
  reflexivity.
Qed.