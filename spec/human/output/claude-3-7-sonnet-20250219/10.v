From Coq Require Import Ascii String List Arith Lia.
Import ListNotations.
Open Scope string_scope.

(* 回文定义：反转后等于自己 *)
Definition palindrome (s : string) : Prop :=
  s = string_of_list_ascii (List.rev (list_ascii_of_string s)).

(* 规格定义：最短的回文，且以 input 为前缀 *)
Definition problem_10_spec (input output : string) : Prop :=
  prefix input output = true /\
  palindrome output /\
  forall p : string,
    prefix input p = true /\
    palindrome p ->
    String.length output <= String.length p.

Example problem_10_spec_empty :
  problem_10_spec "" "".
Proof.
  unfold problem_10_spec.
  split.
  - (* prefix "" "" = true *)
    simpl. reflexivity.
  - split.
    + (* palindrome "" *)
      unfold palindrome.
      simpl.
      reflexivity.
    + (* minimal length: for any p prefix "" p and palindrome p, length "" <= length p *)
      intros p [Hpref Hpal].
      (* prefix "" p = true always holds *)
      (* length "" = 0 thus 0 <= length p *)
      simpl.
      apply Nat.le_0_l.
Qed.