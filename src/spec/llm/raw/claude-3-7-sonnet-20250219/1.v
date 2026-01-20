
Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.

Definition balanced_paren_group (s : string) : Prop :=
  let fix aux (i : nat) (count : Z) : option Z :=
      match nth_error s i with
      | None => if count =? 0 then Some 0 else None
      | Some c =>
        let count' :=
          if Ascii.ascii_dec c " "((*space*) ) then count
          else if Ascii.ascii_dec c "(" then count + 1
          else if Ascii.ascii_dec c ")" then count - 1
          else count in
        if count' <? 0 then None
        else aux (i + 1) count'
      end in
  aux 0 0 = Some 0 /\ count_parens s = 0.

Fixpoint count_parens (s : string) : Z :=
  match s with
  | EmptyString => 0
  | String c rest =>
    (if Ascii.ascii_dec c "(" then 1 else 0) -
    (if Ascii.ascii_dec c ")" then 1 else 0) + count_parens rest
  end.

Definition no_space_string (s : string) : Prop :=
  forall i c, nth_error s i = Some c -> c <> " ".

Definition separate_paren_groups_spec (paren_string : string) (groups : list string) : Prop :=
  let fix all_balanced (l : list string) : Prop :=
      match l with
      | [] => True
      | g :: tl => balanced_paren_group g /\ no_space_string g /\ all_balanced tl
      end in
  (* The concatenation of groups equals the input string with spaces removed *)
  let s_no_space := filter (fun c => if Ascii.ascii_dec c " " then false else true) (list_ascii_of_string paren_string) in
  let concat_groups := fold_left (fun acc g => acc ++ (list_ascii_of_string g)) groups [] in
  all_balanced groups /\
  concat_groups = s_no_space /\
  (* Groups are separated balanced groups with no nesting between them *)
  (forall g, In g groups -> balanced_paren_group g).
