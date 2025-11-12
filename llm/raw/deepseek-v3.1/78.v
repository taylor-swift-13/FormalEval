
Require Import List Ascii String.
Import ListNotations.

Definition hex_key_spec (num : string) (result : nat) : Prop :=
  result = length (filter (fun c => 
    match c with
    | "2" | "3" | "5" | "7" | "B" | "D" => true
    | _ => false
    end) (list_ascii_of_string num)).
