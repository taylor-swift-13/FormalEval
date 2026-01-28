Require Import ZArith Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Nat.

(* Enable scopes for convenient notation *)
Open Scope string_scope.
Open Scope nat_scope.

Definition char_to_digit (c : ascii) : nat :=
  nat_of_ascii c - nat_of_ascii "0"%char.

(* 辅助函数：将字符串转换为自然数 *)
Fixpoint string_to_nat_aux (s : string) (acc : nat) : nat :=
  match s with
  | EmptyString => acc
  | String c s' => string_to_nat_aux s' (acc * 10 + char_to_digit c)
  end.

(* 主函数：将字符串转换为自然数 *)
Definition string_to_nat (s : string) : nat :=
  string_to_nat_aux s 0.

(*
  辅助规约: parse_fruit_string
  这个规约描述了从输入字符串 s 中解析出苹果和橘子数量的逻辑。
*)
Definition parse_fruit_string (s : string) (apples oranges : nat) : Prop :=
  exists s_apples s_oranges,
    apples = string_to_nat s_apples /\
    oranges = string_to_nat s_oranges /\
    s = (s_apples ++ " apples and " ++ s_oranges ++ " oranges")%string.
       

Definition problem_67_pre (s : string) (n : nat) : Prop := True.

Definition problem_67_spec (s : string) (n : nat) (ret : nat) : Prop :=
  exists apples oranges,
    parse_fruit_string s apples oranges /\
    ret = n - (apples + oranges).

(* Example Proof *)
Example test_fruit_distribution : problem_67_spec "3 apples and 7 oranges" 26 16.
Proof.
  (* Unfold the specification to see the goal *)
  unfold problem_67_spec.
  
  (* Provide the witnesses for apples and oranges *)
  exists 3, 7.
  
  (* Split the goal into the parsing part and the calculation part *)
  split.
  
  - (* Sub-goal 1: Prove parse_fruit_string *)
    unfold parse_fruit_string.
    (* Provide the substring witnesses *)
    exists "3", "7".
    
    (* Verify the components of the parsing *)
    split.
    + (* Verify apples = string_to_nat "3" *)
      simpl. reflexivity.
    + split.
      * (* Verify oranges = string_to_nat "7" *)
        simpl. reflexivity.
      * (* Verify the string reconstruction *)
        simpl. reflexivity.
        
  - (* Sub-goal 2: Prove the arithmetic calculation *)
    (* 16 = 26 - (3 + 7) *)
    simpl. reflexivity.
Qed.