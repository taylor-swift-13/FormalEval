From Coq Require Import Ascii String List Arith Lia.
Import ListNotations.
Open Scope string_scope.

Definition palindrome (s : string) : Prop :=
  s = string_of_list_ascii (List.rev (list_ascii_of_string s)).

Definition problem_10_pre : Prop := True.

Definition problem_10_spec (input output : string) : Prop :=
  prefix input output = true /\
  palindrome output /\
 forall p : string,
    prefix input p = true /\
    palindrome p ->
    String.length output <= String.length p.

Example test_problem_10 : problem_10_spec "erace" "eracecare".
Proof.
  unfold problem_10_spec.
  split.
  - simpl. reflexivity.
  - split.
    + unfold palindrome.
      simpl. reflexivity.
    + intros p [Hprefix Hpal].
      simpl.
      unfold prefix in Hprefix.
      unfold palindrome in Hpal.
      destruct p as [|a0 p0]; simpl in Hprefix; try discriminate.
      destruct p0 as [|a1 p1]; simpl in Hprefix; try discriminate.
      destruct p1 as [|a2 p2]; simpl in Hprefix; try discriminate.
      destruct p2 as [|a3 p3]; simpl in Hprefix; try discriminate.
      destruct p3 as [|a4 p4]; simpl in Hprefix; try discriminate.
      simpl. lia.
Qed.