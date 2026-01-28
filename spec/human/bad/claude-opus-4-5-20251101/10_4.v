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

Example test_problem_10 : problem_10_spec "xyx" "xyx".
Proof.
  unfold problem_10_spec.
  split.
  - simpl. reflexivity.
  - split.
    + unfold palindrome.
      simpl. reflexivity.
    + intros p [Hprefix Hpal].
      simpl.
      assert (H: String.length "xyx" = 3) by reflexivity.
      assert (H2: 3 <= String.length p).
      {
        clear Hpal.
        destruct p as [| c1 p1]; simpl in Hprefix; try discriminate.
        destruct p1 as [| c2 p2]; simpl in Hprefix; try discriminate.
        destruct p2 as [| c3 p3]; simpl in Hprefix; try discriminate.
        simpl. lia.
      }
      exact H2.
Qed.