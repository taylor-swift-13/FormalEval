From Coq Require Import Ascii String List Arith Lia.
Import ListNotations.
Open Scope string_scope.

(* 回文定义：反转后等于自己 *)
Definition palindrome (s : string) : Prop :=
  s = string_of_list_ascii (List.rev (list_ascii_of_string s)).

(* 定义前缀判断函数 *)
Fixpoint prefix (a b : string) : bool :=
  match a, b with
  | EmptyString, _ => true
  | String a1 a2, String b1 b2 =>
      if Ascii.eqb a1 b1 then prefix a2 b2 else false
  | _, _ => false
  end.

Definition problem_10_pre : Prop := True.

(* 规格定义：最短的回文，且以 input 为前缀 *)
Definition problem_10_spec (input output : string) : Prop :=
  prefix input output = true /\
  palindrome output /\
  forall p : string,
    prefix input p = true /\
    palindrome p ->
    String.length output <= String.length p.

Example problem_10_test_case_dewed :
  problem_10_spec "dewed" "dewed".
Proof.
  unfold problem_10_spec.
  split.
  - unfold prefix. simpl. reflexivity.
  - split.
    + unfold palindrome. simpl. reflexivity.
    + intros p [Hpref Hpal].
      assert (forall s t, prefix s t = true -> String.length s <= String.length t) as Hlen.
      { intros s.
        induction s as [| a s IH]; intros t H; simpl in H.
        - simpl. lia.
        - destruct t as [| b t]; simpl in H; try discriminate H.
          destruct (Ascii.eqb a b) eqn:E; simpl in H; try discriminate H.
          specialize (IH t H). simpl. lia.
      }
      apply (Hlen "dewed" p). exact Hpref.
Qed.