Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Import ListNotations.

Open Scope string_scope.
Open Scope list_scope.

(* 空格字符 *)
Definition space : ascii := Ascii.ascii_of_nat 32.

(* 判断是否为英文字母 (A-Z 或 a-z) *)
Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122).

(* 判定：s 是否以单个字母作为最后的 token（最后字符是字母，且前一字符要么不存在要么是空格） *)
(* Explicitly type 'pre' and 'c' to avoid type inference ambiguity with string/list scopes *)
Definition ends_with_single_letter_pred (s : string) : Prop :=
  let l := list_ascii_of_string s in
  exists (pre : list ascii) (c : ascii),
    l = pre ++ [c] /\
    is_alpha c /\
    (pre = [] \/ exists (pre' : list ascii), pre = pre' ++ [space]).

(* 任意字符列表均可 *)
Definition problem_134_pre (s : string) : Prop := True.

(* 最终 Spec：输入 s，输出 b。当且仅当 ends_with_single_letter_pred s 成立时返回 true。 *)
Definition problem_134_spec (s : string) (b : bool) : Prop :=
  b = true <-> ends_with_single_letter_pred s.

Example test_apple : problem_134_spec "apple" false.
Proof.
  unfold problem_134_spec.
  split.
  - (* false = true -> ... *)
    intros H. discriminate.
  - (* ... -> false = true *)
    intros H.
    unfold ends_with_single_letter_pred in H.
    simpl in H.
    destruct H as [pre [c [Heq [Halpha Hcond]]]].
    
    (* Decompose 'pre' based on the length of "apple" (5).
       Since l = pre ++ [c], pre must have length 4. *)
    destruct pre. { simpl in Heq. discriminate. }
    destruct pre. { simpl in Heq. discriminate. }
    destruct pre. { simpl in Heq. discriminate. }
    destruct pre. { simpl in Heq. discriminate. }
    destruct pre.
    2: { 
      (* Case where pre has length >= 5 *)
      simpl in Heq. injection Heq. intros. 
      destruct pre; discriminate. 
    }
    
    (* Now pre is known to be a list of 4 elements. 
       Heq simplifies to: [a;p;p;l;e] = [a0;a1;a2;a3;c] *)
    simpl in Heq. inversion Heq. subst.
    (* We identified c='e' and pre=['a'; 'p'; 'p'; 'l'] *)
    
    (* Check the condition on pre *)
    destruct Hcond as [Hnil | [pre' Hspace]].
    + (* Case: pre is empty *)
      discriminate.
    + (* Case: pre ends with space *)
      (* pre has length 4. pre' ++ [space] must have length 4, so pre' has length 3 *)
      destruct pre'. { simpl in Hspace. discriminate. }
      destruct pre'. { simpl in Hspace. discriminate. }
      destruct pre'. { simpl in Hspace. discriminate. }
      destruct pre'.
      2: { simpl in Hspace. destruct pre'; discriminate. }
      
      (* Extract the last character of pre and compare with space *)
      simpl in Hspace. inversion Hspace.
      (* H2: l = space *)
      (* 'l' is ascii 108, space is ascii 32 *)
      unfold space in H2.
      
      (* Evaluate the ascii values to constructors to derive a contradiction *)
      cbv in H2.
      discriminate.
Qed.