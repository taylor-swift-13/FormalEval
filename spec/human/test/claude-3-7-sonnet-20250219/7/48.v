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
     "How vexingly quick daft zebras jump";
     "Jackdaws love my big sphinx of quartz"]
    []
    "oConstitutionx".
Proof.
  unfold problem_7_spec.
  simpl.
  repeat (
    match goal with
    | |- context [contains_substring ?s "oConstitutionx"] =>
      unfold contains_substring; simpl;
      (* progressively reduce with prefix tests *)
      repeat (
        match goal with
        | |- context [String.prefix "oConstitutionx" ?str] =>
          unfold String.prefix; simpl
        end
      )
    end
  ).
  reflexivity.
Qed.