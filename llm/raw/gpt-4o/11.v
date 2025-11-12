
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Definition string_xor_spec (a b result : string) : Prop :=
  forall i : nat,
    i < String.length a ->
    i < String.length b ->
    nth i (map (fun x => if x then "1" else "0") (map (fun p => xorb (fst p) (snd p)) (combine (map (fun c => if c =? "1" then true else false) (list_of_string a)) (map (fun c => if c =? "1" then true else false) (list_of_string b))))) "") = String.get i result.
