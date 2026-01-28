Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope char_scope.

(* The definitions from the specification, with minor type adjustments for compilation 
   (ensuring characters like " " are treated as ascii, not string). *)

Fixpoint count_depth_aux (l : list ascii) (cnt : Z) (max_d : Z) : Z :=
  match l with
  | [] => max_d
  | c :: cs =>
    let cnt' := if ascii_dec c "(" then (cnt + 1)
                else if ascii_dec c ")" then (cnt - 1)
                else cnt in
    let max_d' := Z.max max_d cnt' in
    count_depth_aux cs cnt' max_d'
  end.

Definition count_depth (s : string) : Z :=
  count_depth_aux (list_ascii_of_string s) 0 0.

Fixpoint split_and_filter (l : list ascii) (acc : list ascii) : list string :=
  match l with
  | [] => match acc with
          | [] => []
          | _ => [string_of_list_ascii (rev acc)]
          end
  | c :: cs =>
      if ascii_dec c " " then
        match acc with
        | [] => split_and_filter cs []
        | _ => (string_of_list_ascii (rev acc)) :: (split_and_filter cs [])
        end
      else
        split_and_filter cs (c :: acc)
  end.

Definition parse_nested_parens_spec (paren_string : string) (result : list Z) : Prop :=
  result = map count_depth (split_and_filter (list_ascii_of_string paren_string) []).

(* The Example Proof *)

Example test_nested_parens : 
  parse_nested_parens_spec "()()()()()()" [1].
Proof.
  (* Step 1: Unfold the specification definition *)
  unfold parse_nested_parens_spec.

  (* Step 2: Perform computation. 
     vm_compute is efficient for evaluating string parsing and integer arithmetic 
     down to their normal forms. *)
  vm_compute.

  (* Step 3: Verify that the computed result matches the expected list. *)
  reflexivity.
Qed.