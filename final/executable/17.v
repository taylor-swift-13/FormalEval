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

Fixpoint parse_note (note : list ascii) : option nat :=
  match note with
  | ["o"%char] => Some 4
  | ["o"%char; "|"%char] => Some 2
  | ["."%char; "|"%char] => Some 1
  | _ => None
  end.

Fixpoint parse_music_impl_aux (notes : list (list ascii)) : list nat :=
  match notes with
  | [] => []
  | note :: rest =>
    match parse_note note with
    | Some n => n :: parse_music_impl_aux rest
    | None => parse_music_impl_aux rest
    end
  end.

Definition parse_music_impl (input : list ascii) : list nat :=
  parse_music_impl_aux (SplitOnSpaces input).

Definition parse_music_Spec (input : list ascii) (output : list nat) : Prop :=
  output = parse_music_impl input.
