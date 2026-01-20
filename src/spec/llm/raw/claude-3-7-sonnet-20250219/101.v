
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition words_string_spec (s : string) (result : list string) : Prop :=
  exists words : list string,
    (forall w, In w words -> w <> "") /\
    (forall w, In w (map (fun c => if Ascii.eqb c "," then " " else String c EmptyString) s) = false) /\
    result = filter (fun w => negb (String.eqb w "")) (String.split (fun c => Ascii.eqb c " " ) (String.map (fun c => if Ascii.eqb c "," then " " else c) s)).
