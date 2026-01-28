Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

(* 定义字符串是否为小写的谓词 *)
Definition is_lowercase (s : string) : Prop :=
  Forall (fun c => (("a" <=? c)%char && (c <=? "z")%char) = true) (list_ascii_of_string s).

(* 定义字符串是否为大写的谓词 *)
Definition is_uppercase (s : string) : Prop :=
  Forall (fun c => (("A" <=? c)%char && (c <=? "Z")%char) = true) (list_ascii_of_string s).

(* 定义键的类型，可以是字符串或其他类型 *)
Inductive KeyType :=
  | KeyString (s : string)
  | KeyOther.

(* 定义字典的类型，键为 KeyType，值为字符串 *)
Definition dictionary := list (KeyType * string).

(* 字典类型已保证键值均为字符串，无附加约束；空字典由规约处理 *)
Definition problem_95_pre (d : dictionary) : Prop := True.

(* check_dict_case 函数的规约 *)
Definition problem_95_spec (d : dictionary) (output : bool) : Prop :=
  match d with
  | [] => output = false
  | _ =>
    ( (forall k v, In (k, v) d -> match k with KeyString s => is_lowercase s | KeyOther => False end) \/
      (forall k v, In (k, v) d -> match k with KeyString s => is_uppercase s | KeyOther => False end) )
    <-> output = true
  end.

Example test_problem_95 : problem_95_spec [(KeyString "first_name", "oJohn"); (KeyString "Last_Name", "Doe"); (KeyString "city", "New York")] false.
Proof.
  (* Unfold the specification *)
  unfold problem_95_spec.
  
  (* Simplify the match expression on the non-empty list *)
  simpl.
  
  (* Split the bi-implication: (AllLower \/ AllUpper) <-> false = true *)
  split.
  
  - (* Direction: (AllLower \/ AllUpper) -> False *)
    intros [H_lower | H_upper].
    
    + (* Case 1: Assumption that all keys are lowercase *)
      (* We use "Last_Name" as a counter-example because it contains uppercase letters *)
      assert (H_in : In (KeyString "Last_Name", "Doe") 
        [(KeyString "first_name", "oJohn"); (KeyString "Last_Name", "Doe"); (KeyString "city", "New York")]).
      { simpl. right. left. reflexivity. }
      
      (* Apply the assumption to the counter-example *)
      apply H_lower in H_in.
      simpl in H_in.
      unfold is_lowercase in H_in.
      
      (* "Last_Name" starts with 'L', so the Forall property must hold for 'L' *)
      inversion H_in as [| x l H_head H_tail]. subst.
      
      (* Verify that 'L' is not in range ['a', 'z'] *)
      vm_compute in H_head.
      discriminate H_head.
      
    + (* Case 2: Assumption that all keys are uppercase *)
      (* We use "first_name" as a counter-example because it contains lowercase letters *)
      assert (H_in : In (KeyString "first_name", "oJohn") 
        [(KeyString "first_name", "oJohn"); (KeyString "Last_Name", "Doe"); (KeyString "city", "New York")]).
      { simpl. left. reflexivity. }
      
      (* Apply the assumption to the counter-example *)
      apply H_upper in H_in.
      simpl in H_in.
      unfold is_uppercase in H_in.
      
      (* "first_name" starts with 'f', so the Forall property must hold for 'f' *)
      inversion H_in as [| x l H_head H_tail]. subst.
      
      (* Verify that 'f' is not in range ['A', 'Z'] *)
      vm_compute in H_head.
      discriminate H_head.
      
  - (* Direction: False -> (AllLower \/ AllUpper) *)
    intros H_false.
    discriminate H_false.
Qed.