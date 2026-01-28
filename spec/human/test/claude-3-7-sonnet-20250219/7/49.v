Require Import List.
Require Import String.
Import ListNotations.

Open Scope string_scope.

Fixpoint contains_substring (s sub : string) : bool :=
  match s with
  | EmptyString => if String.eqb sub EmptyString then true else false
  | String _ rest =>
      if String.prefix sub s then true
      else contains_substring rest sub
  end.

Fixpoint filter_by_substring_impl (input : list string) (sub : string) : list string :=
  match input with
  | [] => []
  | h :: t =>
    if contains_substring h sub then
      h :: filter_by_substring_impl t sub
    else
      filter_by_substring_impl t sub
  end.

Definition problem_7_spec (input output : list string) (sub : string) : Prop :=
  output = filter_by_substring_impl input sub.

Example test_case_1 :
  problem_7_spec
    ["The quick brown fox jumps over the lazy dog";
     "Pack my box with five dozen liquor jugs";
     "Jackdaws love my big sphinx of quartz"]
    []
    "created".
Proof.
  unfold problem_7_spec.
  simpl.
  repeat (
    match goal with
    | |- context [contains_substring ?s "created"] =>
      let H := fresh "H" in
      assert (H: contains_substring s "created" = false);
      [unfold contains_substring;
       revert s;
       induction s as [| c s' IH];
       simpl;
       try (rewrite String.eqb_refl; discriminate);
       try (simpl;
            destruct (String.prefix "created" (String c s')) eqn:Pf;
            [inversion 1|]);
       destruct (String.eqb "created" EmptyString) eqn:E;
       [discriminate|];
       specialize (IH);
       unfold String.prefix in Pf;
       try exact IH
      | rewrite H; clear H]
    end).
  reflexivity.
Qed.