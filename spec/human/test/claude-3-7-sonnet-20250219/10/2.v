From Coq Require Import Ascii String List Arith Lia.
Import ListNotations.
Open Scope string_scope.

Definition palindrome (s : string) : Prop :=
  s = string_of_list_ascii (List.rev (list_ascii_of_string s)).

Definition problem_10_spec (input output : string) : Prop :=
  prefix input output = true /\
  palindrome output /\
  forall p : string,
    prefix input p = true /\
    palindrome p ->
    String.length output <= String.length p.

Example problem_10_spec_x :
  problem_10_spec "x" "x".
Proof.
  unfold problem_10_spec.
  split.
  - simpl. reflexivity.
  - split.
    + unfold palindrome.
      simpl.
      reflexivity.
    + intros p [Hpref Hpal].
      simpl in Hpref.
      destruct p as [|c p'] eqn:Hp.
      * simpl in Hpref. discriminate Hpref.
      * simpl in Hpref.
        inversion Hpref; subst.
        simpl.
        lia.
Qed.