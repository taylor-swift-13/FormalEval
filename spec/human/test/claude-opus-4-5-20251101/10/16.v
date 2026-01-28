From Coq Require Import Ascii String List Arith Lia.
Import ListNotations.
Open Scope string_scope.

(* 回文定义：反转后等于自己 *)
Definition palindrome (s : string) : Prop :=
  s = string_of_list_ascii (List.rev (list_ascii_of_string s)).

Definition problem_10_pre : Prop := True.

(* 规格定义：最短的回文，且以 input 为前缀 *)
Definition problem_10_spec (input output : string) : Prop :=
  prefix input output = true /\
  palindrome output /\
 forall p : string,
    prefix input p = true /\
    palindrome p ->
    String.length output <= String.length p.

(* Test case: input = "r", output = "r" *)
Example test_problem_10 : problem_10_spec "r" "r".
Proof.
  unfold problem_10_spec.
  split.
  - (* prefix "r" "r" = true *)
    simpl. reflexivity.
  - split.
    + (* palindrome "r" *)
      unfold palindrome.
      simpl. reflexivity.
    + (* forall p, prefix "r" p = true /\ palindrome p -> length "r" <= length p *)
      intros p [Hprefix Hpal].
      destruct p as [| c p'].
      * simpl in Hprefix. discriminate.
      * simpl. lia.
Qed.