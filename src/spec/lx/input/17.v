(* """ Input to this function is a string representing musical notes in a special ASCII format.
Your task is to parse this string and return list of integers corresponding to how many beats does each
not last.

Here is a legend:
'o' - whole note, lasts four beats
'o|' - half note, lasts two beats
'.|' - quater note, lasts one beat

>>> parse_music('o o| .| o| o| .| .| .| .| o o')
[4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4]
""" *)

(* 
*)

Require Import Ascii String List.
Import ListNotations.

Fixpoint SplitOnSpaces_aux (current_group : list ascii) (S : list ascii) : list (list ascii) :=
  match S with
  | [] =>
    match current_group with
    | [] => []
    | _ => [List.rev current_group]
    end
  | h :: t =>
    if ascii_dec h " "%char then
      match current_group with
      | [] => SplitOnSpaces_aux [] t (* 多个或前导空格 *)
      | _ => (List.rev current_group) :: SplitOnSpaces_aux [] t
      end
    else
      SplitOnSpaces_aux (h :: current_group) t
  end.

Definition SplitOnSpaces (S : list ascii) : list (list ascii) :=
  SplitOnSpaces_aux [] S.

Definition parse_music_Spec (input : list ascii) (output : list nat) : Prop :=
  let splited_input := SplitOnSpaces input in
  length splited_input = length output /\
  forall i note,
    nth_error splited_input i = Some note ->
    nth_error output i =
      match note with
      | ["o"%char] => Some 4
      | ["o"%char; "|"%char] => Some 2
      | ["."%char; "|"%char] => Some 1
      | _ => None (* 非法输入*)
      end.
